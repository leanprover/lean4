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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(lean_object* v_x_181_, lean_object* v_x_182_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_x_189_, v_x_190_);
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
uint8_t v___x_43464__boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___x_43464__boxed_220_ = lean_unbox(v___x_216_);
v_res_221_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_43464__boxed_220_, v_env_217_, v_n_218_, v_x_219_);
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
lean_object* v___x_245_; lean_object* v_env_246_; uint8_t v___x_247_; lean_object* v_env_248_; lean_object* v___x_249_; lean_object* v_toCold_250_; lean_object* v_mctx_251_; lean_object* v_lctx_252_; lean_object* v_options_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_245_ = lean_st_ref_get(v___y_243_);
v_env_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_env_246_);
lean_dec(v___x_245_);
v___x_247_ = 0;
v_env_248_ = l_Lean_Environment_setRecordingDeps(v_env_246_, v___x_247_);
v___x_249_ = lean_st_ref_get(v___y_241_);
v_toCold_250_ = lean_ctor_get(v___y_242_, 0);
v_mctx_251_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_mctx_251_);
lean_dec(v___x_249_);
v_lctx_252_ = lean_ctor_get(v___y_240_, 2);
v_options_253_ = lean_ctor_get(v_toCold_250_, 2);
lean_inc_ref(v_options_253_);
lean_inc_ref(v_lctx_252_);
v___x_254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_254_, 0, v_env_248_);
lean_ctor_set(v___x_254_, 1, v_mctx_251_);
lean_ctor_set(v___x_254_, 2, v_lctx_252_);
lean_ctor_set(v___x_254_, 3, v_options_253_);
v___x_255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_msgData_239_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object* v_msgData_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_272_, uint8_t v___y_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 1)
{
lean_object* v_pre_275_; 
v_pre_275_ = lean_ctor_get(v_x_274_, 0);
switch(lean_obj_tag(v_pre_275_))
{
case 1:
{
lean_object* v_pre_276_; 
v_pre_276_ = lean_ctor_get(v_pre_275_, 0);
switch(lean_obj_tag(v_pre_276_))
{
case 0:
{
lean_object* v_str_277_; lean_object* v_str_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_str_277_ = lean_ctor_get(v_x_274_, 1);
v_str_278_ = lean_ctor_get(v_pre_275_, 1);
v___x_279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_280_ = lean_string_dec_eq(v_str_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_282_ = lean_string_dec_eq(v_str_278_, v___x_281_);
if (v___x_282_ == 0)
{
return v___x_282_;
}
else
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_284_ = lean_string_dec_eq(v_str_277_, v___x_283_);
if (v___x_284_ == 0)
{
return v___x_284_;
}
else
{
return v_suppressElabErrors_272_;
}
}
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_286_ = lean_string_dec_eq(v_str_277_, v___x_285_);
if (v___x_286_ == 0)
{
return v___x_286_;
}
else
{
return v_suppressElabErrors_272_;
}
}
}
case 1:
{
lean_object* v_pre_287_; 
v_pre_287_ = lean_ctor_get(v_pre_276_, 0);
if (lean_obj_tag(v_pre_287_) == 0)
{
lean_object* v_str_288_; lean_object* v_str_289_; lean_object* v_str_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_str_288_ = lean_ctor_get(v_x_274_, 1);
v_str_289_ = lean_ctor_get(v_pre_275_, 1);
v_str_290_ = lean_ctor_get(v_pre_276_, 1);
v___x_291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_292_ = lean_string_dec_eq(v_str_290_, v___x_291_);
if (v___x_292_ == 0)
{
return v___x_292_;
}
else
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_294_ = lean_string_dec_eq(v_str_289_, v___x_293_);
if (v___x_294_ == 0)
{
return v___x_294_;
}
else
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_296_ = lean_string_dec_eq(v_str_288_, v___x_295_);
if (v___x_296_ == 0)
{
return v___x_296_;
}
else
{
return v_suppressElabErrors_272_;
}
}
}
}
else
{
return v___y_273_;
}
}
default: 
{
return v___y_273_;
}
}
}
case 0:
{
lean_object* v_str_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_str_297_ = lean_ctor_get(v_x_274_, 1);
v___x_298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_299_ = lean_string_dec_eq(v_str_297_, v___x_298_);
if (v___x_299_ == 0)
{
return v___x_299_;
}
else
{
return v_suppressElabErrors_272_;
}
}
default: 
{
return v___y_273_;
}
}
}
else
{
return v___y_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_300_, lean_object* v___y_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_suppressElabErrors_boxed_303_; uint8_t v___y_43548__boxed_304_; uint8_t v_res_305_; lean_object* v_r_306_; 
v_suppressElabErrors_boxed_303_ = lean_unbox(v_suppressElabErrors_300_);
v___y_43548__boxed_304_ = lean_unbox(v___y_301_);
v_res_305_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_303_, v___y_43548__boxed_304_, v_x_302_);
lean_dec(v_x_302_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_308_, lean_object* v_msgData_309_, uint8_t v_severity_310_, uint8_t v_isSilent_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; uint8_t v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v_toCold_325_; lean_object* v___y_326_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___y_394_; uint8_t v___x_405_; uint8_t v___y_407_; uint8_t v___y_408_; uint8_t v___y_409_; uint8_t v___y_411_; uint8_t v___x_419_; 
v___x_405_ = 2;
v___x_419_ = l_Lean_instBEqMessageSeverity_beq(v_severity_310_, v___x_405_);
if (v___x_419_ == 0)
{
v___y_411_ = v___x_419_;
goto v___jp_410_;
}
else
{
uint8_t v___x_420_; 
lean_inc_ref(v_msgData_309_);
v___x_420_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_309_);
v___y_411_ = v___x_420_;
goto v___jp_410_;
}
v___jp_317_:
{
lean_object* v_currNamespace_327_; lean_object* v_openDecls_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_env_333_; lean_object* v_nextMacroScope_334_; lean_object* v_ngen_335_; lean_object* v_auxDeclNGen_336_; lean_object* v_traceState_337_; lean_object* v_cache_338_; lean_object* v_recordedDeps_339_; lean_object* v_messages_340_; lean_object* v_infoState_341_; lean_object* v_snapshotTasks_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_353_; 
v_currNamespace_327_ = lean_ctor_get(v_toCold_325_, 4);
v_openDecls_328_ = lean_ctor_get(v_toCold_325_, 5);
lean_inc(v_openDecls_328_);
lean_inc(v_currNamespace_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_currNamespace_327_);
lean_ctor_set(v___x_329_, 1, v_openDecls_328_);
v___x_330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___y_324_);
lean_inc_ref(v___y_321_);
lean_inc_ref(v___y_320_);
v___x_331_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_331_, 0, v___y_320_);
lean_ctor_set(v___x_331_, 1, v___y_318_);
lean_ctor_set(v___x_331_, 2, v___y_323_);
lean_ctor_set(v___x_331_, 3, v___y_321_);
lean_ctor_set(v___x_331_, 4, v___x_330_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5, v___y_319_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5 + 1, v___y_322_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5 + 2, v_isSilent_311_);
v___x_332_ = lean_st_ref_take(v___y_326_);
v_env_333_ = lean_ctor_get(v___x_332_, 0);
v_nextMacroScope_334_ = lean_ctor_get(v___x_332_, 1);
v_ngen_335_ = lean_ctor_get(v___x_332_, 2);
v_auxDeclNGen_336_ = lean_ctor_get(v___x_332_, 3);
v_traceState_337_ = lean_ctor_get(v___x_332_, 4);
v_cache_338_ = lean_ctor_get(v___x_332_, 5);
v_recordedDeps_339_ = lean_ctor_get(v___x_332_, 6);
v_messages_340_ = lean_ctor_get(v___x_332_, 7);
v_infoState_341_ = lean_ctor_get(v___x_332_, 8);
v_snapshotTasks_342_ = lean_ctor_get(v___x_332_, 9);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_353_ == 0)
{
v___x_344_ = v___x_332_;
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snapshotTasks_342_);
lean_inc(v_infoState_341_);
lean_inc(v_messages_340_);
lean_inc(v_recordedDeps_339_);
lean_inc(v_cache_338_);
lean_inc(v_traceState_337_);
lean_inc(v_auxDeclNGen_336_);
lean_inc(v_ngen_335_);
lean_inc(v_nextMacroScope_334_);
lean_inc(v_env_333_);
lean_dec(v___x_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = lean_box(0);
v___x_347_ = l_Lean_MessageLog_add(v___x_331_, v_messages_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 7, v___x_347_);
v___x_349_ = v___x_344_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_env_333_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_nextMacroScope_334_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_ngen_335_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_auxDeclNGen_336_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_traceState_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_cache_338_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_recordedDeps_339_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v_infoState_341_);
lean_ctor_set(v_reuseFailAlloc_352_, 9, v_snapshotTasks_342_);
v___x_349_ = v_reuseFailAlloc_352_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_st_ref_put(v___y_326_, v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_346_);
return v___x_351_;
}
}
}
v___jp_354_:
{
lean_object* v_fileName_363_; lean_object* v_fileMap_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_380_; 
v_fileName_363_ = lean_ctor_get(v___y_357_, 0);
v_fileMap_364_ = lean_ctor_get(v___y_357_, 1);
v___x_365_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_309_);
v___x_366_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_365_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_380_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_380_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_380_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc_ref_n(v_fileMap_364_, 2);
v___x_371_ = l_Lean_FileMap_toPosition(v_fileMap_364_, v___y_360_);
lean_dec(v___y_360_);
v___x_372_ = l_Lean_FileMap_toPosition(v_fileMap_364_, v___y_362_);
lean_dec(v___y_362_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
v___x_374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_361_ == 0)
{
lean_del_object(v___x_369_);
lean_dec_ref(v___y_356_);
v___y_318_ = v___x_371_;
v___y_319_ = v___y_358_;
v___y_320_ = v_fileName_363_;
v___y_321_ = v___x_374_;
v___y_322_ = v___y_359_;
v___y_323_ = v___x_373_;
v___y_324_ = v_a_367_;
v_toCold_325_ = v___y_355_;
v___y_326_ = v___y_315_;
goto v___jp_317_;
}
else
{
uint8_t v___x_375_; 
lean_inc(v_a_367_);
v___x_375_ = l_Lean_MessageData_hasTag(v___y_356_, v_a_367_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_378_; 
lean_dec_ref_known(v___x_373_, 1);
lean_dec_ref(v___x_371_);
lean_dec(v_a_367_);
v___x_376_ = lean_box(0);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_376_);
v___x_378_ = v___x_369_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
lean_del_object(v___x_369_);
v___y_318_ = v___x_371_;
v___y_319_ = v___y_358_;
v___y_320_ = v_fileName_363_;
v___y_321_ = v___x_374_;
v___y_322_ = v___y_359_;
v___y_323_ = v___x_373_;
v___y_324_ = v_a_367_;
v_toCold_325_ = v___y_355_;
v___y_326_ = v___y_315_;
goto v___jp_317_;
}
}
}
}
v___jp_381_:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Syntax_getTailPos_x3f(v___y_387_, v___y_385_);
lean_dec(v___y_387_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_inc(v___y_388_);
v___y_355_ = v___y_382_;
v___y_356_ = v___y_383_;
v___y_357_ = v___y_382_;
v___y_358_ = v___y_385_;
v___y_359_ = v___y_386_;
v___y_360_ = v___y_388_;
v___y_361_ = v___y_384_;
v___y_362_ = v___y_388_;
goto v___jp_354_;
}
else
{
lean_object* v_val_390_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
v___y_355_ = v___y_382_;
v___y_356_ = v___y_383_;
v___y_357_ = v___y_382_;
v___y_358_ = v___y_385_;
v___y_359_ = v___y_386_;
v___y_360_ = v___y_388_;
v___y_361_ = v___y_384_;
v___y_362_ = v_val_390_;
goto v___jp_354_;
}
}
v___jp_391_:
{
lean_object* v_toCold_395_; lean_object* v_ref_396_; uint8_t v_suppressElabErrors_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___f_400_; lean_object* v_ref_401_; lean_object* v___x_402_; 
v_toCold_395_ = lean_ctor_get(v___y_314_, 0);
v_ref_396_ = lean_ctor_get(v___y_314_, 2);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_314_, sizeof(void*)*3 + 2);
v___x_398_ = lean_box(v_suppressElabErrors_397_);
v___x_399_ = lean_box(v___y_392_);
v___f_400_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_400_, 0, v___x_398_);
lean_closure_set(v___f_400_, 1, v___x_399_);
v_ref_401_ = l_Lean_replaceRef(v_ref_308_, v_ref_396_);
v___x_402_ = l_Lean_Syntax_getPos_x3f(v_ref_401_, v___y_393_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___y_382_ = v_toCold_395_;
v___y_383_ = v___f_400_;
v___y_384_ = v_suppressElabErrors_397_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_394_;
v___y_387_ = v_ref_401_;
v___y_388_ = v___x_403_;
goto v___jp_381_;
}
else
{
lean_object* v_val_404_; 
v_val_404_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v___x_402_, 1);
v___y_382_ = v_toCold_395_;
v___y_383_ = v___f_400_;
v___y_384_ = v_suppressElabErrors_397_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_394_;
v___y_387_ = v_ref_401_;
v___y_388_ = v_val_404_;
goto v___jp_381_;
}
}
v___jp_406_:
{
if (v___y_409_ == 0)
{
v___y_392_ = v___y_407_;
v___y_393_ = v___y_408_;
v___y_394_ = v_severity_310_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___y_407_;
v___y_393_ = v___y_408_;
v___y_394_ = v___x_405_;
goto v___jp_391_;
}
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 1;
v___x_413_ = l_Lean_instBEqMessageSeverity_beq(v_severity_310_, v___x_412_);
if (v___x_413_ == 0)
{
v___y_407_ = v___y_411_;
v___y_408_ = v___y_411_;
v___y_409_ = v___x_413_;
goto v___jp_406_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_314_);
v___x_415_ = l_Lean_warningAsError;
v___x_416_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_414_, v___x_415_);
lean_dec_ref(v___x_414_);
v___y_407_ = v___y_411_;
v___y_408_ = v___y_411_;
v___y_409_ = v___x_416_;
goto v___jp_406_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_msgData_309_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_421_, lean_object* v_msgData_422_, lean_object* v_severity_423_, lean_object* v_isSilent_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
uint8_t v_severity_boxed_430_; uint8_t v_isSilent_boxed_431_; lean_object* v_res_432_; 
v_severity_boxed_430_ = lean_unbox(v_severity_423_);
v_isSilent_boxed_431_ = lean_unbox(v_isSilent_424_);
v_res_432_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_421_, v_msgData_422_, v_severity_boxed_430_, v_isSilent_boxed_431_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v_ref_421_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_433_, uint8_t v_severity_434_, uint8_t v_isSilent_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_ref_441_; lean_object* v___x_442_; 
v_ref_441_ = lean_ctor_get(v___y_438_, 2);
v___x_442_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_441_, v_msgData_433_, v_severity_434_, v_isSilent_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_443_, lean_object* v_severity_444_, lean_object* v_isSilent_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v_severity_boxed_451_; uint8_t v_isSilent_boxed_452_; lean_object* v_res_453_; 
v_severity_boxed_451_ = lean_unbox(v_severity_444_);
v_isSilent_boxed_452_ = lean_unbox(v_isSilent_445_);
v_res_453_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_443_, v_severity_boxed_451_, v_isSilent_boxed_452_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v___x_460_ = 1;
v___x_461_ = 0;
v___x_462_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_454_, v___x_460_, v___x_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_471_);
v___x_474_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_473_, v_opt_470_);
lean_dec_ref(v___x_473_);
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_477_, v___y_478_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v_opt_477_);
return v_res_480_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v_env_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_516_; 
v___x_493_ = lean_st_ref_get(v___y_491_);
v_env_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_env_494_);
lean_dec(v___x_493_);
v___x_495_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_496_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_495_, v___y_490_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_516_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_516_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_516_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v_isExporting_506_; 
v_isExporting_506_ = lean_ctor_get_uint8(v_env_494_, sizeof(void*)*13);
lean_dec_ref(v_env_494_);
if (v_isExporting_506_ == 0)
{
lean_dec(v_a_497_);
lean_dec(v_id_487_);
goto v___jp_501_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = l_Lean_isPrivateName(v_id_487_);
if (v___x_507_ == 0)
{
lean_dec(v_a_497_);
lean_dec(v_id_487_);
goto v___jp_501_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_508_ == 0)
{
lean_dec(v_id_487_);
goto v___jp_501_;
}
else
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_del_object(v___x_499_);
v___x_509_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_510_ = 0;
v___x_511_ = l_Lean_MessageData_ofConstName(v_id_487_, v___x_510_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_509_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_514_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_515_;
}
}
}
v___jp_501_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_box(0);
return v___x_525_;
}
else
{
lean_object* v_head_526_; lean_object* v_tail_527_; lean_object* v_fst_528_; uint8_t v___x_529_; 
v_head_526_ = lean_ctor_get(v_x_524_, 0);
v_tail_527_ = lean_ctor_get(v_x_524_, 1);
v_fst_528_ = lean_ctor_get(v_head_526_, 0);
v___x_529_ = l_Lean_isPrivateName(v_fst_528_);
if (v___x_529_ == 0)
{
v_x_524_ = v_tail_527_;
goto _start;
}
else
{
lean_object* v___x_531_; 
lean_inc(v_head_526_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_head_526_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_532_);
lean_dec(v_x_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_534_, uint8_t v_enableLog_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_toCold_542_; lean_object* v_env_543_; lean_object* v_currNamespace_544_; lean_object* v_openDecls_545_; lean_object* v___x_546_; lean_object* v_res_547_; lean_object* v___x_548_; 
v___x_541_ = lean_st_ref_get(v___y_539_);
v_toCold_542_ = lean_ctor_get(v___y_538_, 0);
v_env_543_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_541_);
v_currNamespace_544_ = lean_ctor_get(v_toCold_542_, 4);
v_openDecls_545_ = lean_ctor_get(v_toCold_542_, 5);
v___x_546_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_538_);
lean_inc(v_openDecls_545_);
lean_inc(v_currNamespace_544_);
v_res_547_ = l_Lean_ResolveName_resolveGlobalName(v_env_543_, v___x_546_, v_currNamespace_544_, v_openDecls_545_, v_id_534_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_st_ref_get(v___y_539_);
if (v_enableLog_535_ == 0)
{
lean_object* v___x_549_; 
lean_dec(v___x_548_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_res_547_);
return v___x_549_;
}
else
{
lean_object* v_env_550_; uint8_t v_isExporting_551_; 
v_env_550_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_env_550_);
lean_dec(v___x_548_);
v_isExporting_551_ = lean_ctor_get_uint8(v_env_550_, sizeof(void*)*13);
lean_dec_ref(v_env_550_);
if (v_isExporting_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_res_547_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_547_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v_fst_555_; lean_object* v___x_556_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v___x_553_, 1);
v_fst_555_ = lean_ctor_get(v_val_554_, 0);
lean_inc(v_fst_555_);
lean_dec(v_val_554_);
v___x_556_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_555_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_564_);
v___x_558_ = v___x_556_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_dec(v___x_556_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_res_547_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_res_547_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_res_547_);
v_a_565_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_556_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_556_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v___x_553_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v_res_547_);
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_574_, lean_object* v_enableLog_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_enableLog_boxed_581_; lean_object* v_res_582_; 
v_enableLog_boxed_581_ = lean_unbox(v_enableLog_575_);
v_res_582_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_574_, v_enableLog_boxed_581_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_583_, lean_object* v_findLocalDecl_x3f_584_, lean_object* v_n_585_, lean_object* v_projs_586_, uint8_t v_globalDeclFound_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v_globalDeclFoundNext_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v_imported_603_; lean_object* v_ctx_604_; lean_object* v_scopes_605_; lean_object* v_givenNameView_606_; uint8_t v___y_608_; 
v_imported_603_ = lean_ctor_get(v_view_583_, 1);
v_ctx_604_ = lean_ctor_get(v_view_583_, 2);
v_scopes_605_ = lean_ctor_get(v_view_583_, 3);
lean_inc(v_scopes_605_);
lean_inc(v_ctx_604_);
lean_inc(v_imported_603_);
lean_inc(v_n_585_);
v_givenNameView_606_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_606_, 0, v_n_585_);
lean_ctor_set(v_givenNameView_606_, 1, v_imported_603_);
lean_ctor_set(v_givenNameView_606_, 2, v_ctx_604_);
lean_ctor_set(v_givenNameView_606_, 3, v_scopes_605_);
if (v_globalDeclFound_587_ == 0)
{
v___y_608_ = v_globalDeclFound_587_;
goto v___jp_607_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = l_List_isEmpty___redArg(v_projs_586_);
if (v___x_643_ == 0)
{
v___y_608_ = v_globalDeclFound_587_;
goto v___jp_607_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = 0;
v___y_608_ = v___x_644_;
goto v___jp_607_;
}
}
v___jp_593_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___y_595_);
lean_ctor_set(v___x_601_, 1, v_projs_586_);
v_n_585_ = v___y_594_;
v_projs_586_ = v___x_601_;
v_globalDeclFound_587_ = v_globalDeclFoundNext_596_;
v___y_588_ = v___y_597_;
v___y_589_ = v___y_598_;
v___y_590_ = v___y_599_;
v___y_591_ = v___y_600_;
goto _start;
}
v___jp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box(v___y_608_);
lean_inc_ref(v_findLocalDecl_x3f_584_);
lean_inc_ref(v_givenNameView_606_);
v___x_610_ = lean_apply_2(v_findLocalDecl_x3f_584_, v_givenNameView_606_, v___x_609_);
if (lean_obj_tag(v___x_610_) == 0)
{
if (lean_obj_tag(v_n_585_) == 1)
{
if (v_globalDeclFound_587_ == 0)
{
lean_object* v_pre_611_; lean_object* v_str_612_; uint8_t v_globalDeclFoundNext_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_pre_611_ = lean_ctor_get(v_n_585_, 0);
lean_inc(v_pre_611_);
v_str_612_ = lean_ctor_get(v_n_585_, 1);
lean_inc_ref(v_str_612_);
lean_dec_ref_known(v_n_585_, 2);
v_globalDeclFoundNext_613_ = 1;
v___x_614_ = l_Lean_MacroScopesView_review(v_givenNameView_606_);
v___x_615_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_614_, v_globalDeclFound_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v_r_618_; uint8_t v___x_619_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_box(0);
v_r_618_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_616_, v___x_617_);
v___x_619_ = l_List_isEmpty___redArg(v_r_618_);
lean_dec(v_r_618_);
if (v___x_619_ == 0)
{
v___y_594_ = v_pre_611_;
v___y_595_ = v_str_612_;
v_globalDeclFoundNext_596_ = v_globalDeclFoundNext_613_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
v___y_599_ = v___y_590_;
v___y_600_ = v___y_591_;
goto v___jp_593_;
}
else
{
v___y_594_ = v_pre_611_;
v___y_595_ = v_str_612_;
v_globalDeclFoundNext_596_ = v_globalDeclFound_587_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
v___y_599_ = v___y_590_;
v___y_600_ = v___y_591_;
goto v___jp_593_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_str_612_);
lean_dec(v_pre_611_);
lean_dec(v_projs_586_);
lean_dec_ref(v_findLocalDecl_x3f_584_);
v_a_620_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_615_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_615_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_pre_628_; lean_object* v_str_629_; 
lean_dec_ref_known(v_givenNameView_606_, 4);
v_pre_628_ = lean_ctor_get(v_n_585_, 0);
lean_inc(v_pre_628_);
v_str_629_ = lean_ctor_get(v_n_585_, 1);
lean_inc_ref(v_str_629_);
lean_dec_ref_known(v_n_585_, 2);
v___y_594_ = v_pre_628_;
v___y_595_ = v_str_629_;
v_globalDeclFoundNext_596_ = v_globalDeclFound_587_;
v___y_597_ = v___y_588_;
v___y_598_ = v___y_589_;
v___y_599_ = v___y_590_;
v___y_600_ = v___y_591_;
goto v___jp_593_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref_known(v_givenNameView_606_, 4);
lean_dec(v_projs_586_);
lean_dec(v_n_585_);
lean_dec_ref(v_findLocalDecl_x3f_584_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref_known(v_givenNameView_606_, 4);
lean_dec(v_n_585_);
lean_dec_ref(v_findLocalDecl_x3f_584_);
v_val_632_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_642_ == 0)
{
v___x_634_ = v___x_610_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v___x_610_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = l_Lean_LocalDecl_toExpr(v_val_632_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_projs_586_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_645_, lean_object* v_findLocalDecl_x3f_646_, lean_object* v_n_647_, lean_object* v_projs_648_, lean_object* v_globalDeclFound_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v_globalDeclFound_boxed_655_; lean_object* v_res_656_; 
v_globalDeclFound_boxed_655_ = lean_unbox(v_globalDeclFound_649_);
v_res_656_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_645_, v_findLocalDecl_x3f_646_, v_n_647_, v_projs_648_, v_globalDeclFound_boxed_655_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_view_645_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_657_, lean_object* v_k_658_){
_start:
{
if (lean_obj_tag(v_t_657_) == 0)
{
lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; uint8_t v___x_663_; 
v_k_659_ = lean_ctor_get(v_t_657_, 1);
v_v_660_ = lean_ctor_get(v_t_657_, 2);
v_l_661_ = lean_ctor_get(v_t_657_, 3);
v_r_662_ = lean_ctor_get(v_t_657_, 4);
v___x_663_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_658_, v_k_659_);
switch(v___x_663_)
{
case 0:
{
v_t_657_ = v_l_661_;
goto _start;
}
case 1:
{
lean_object* v___x_665_; 
lean_inc(v_v_660_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_v_660_);
return v___x_665_;
}
default: 
{
v_t_657_ = v_r_662_;
goto _start;
}
}
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_668_, lean_object* v_k_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_668_, v_k_669_);
lean_dec(v_k_669_);
lean_dec(v_t_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_671_, lean_object* v_givenName_672_){
_start:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = l_Lean_LocalDecl_userName(v_localDecl_671_);
v___x_674_ = lean_name_eq(v___x_673_, v_givenName_672_);
lean_dec(v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_localDecl_671_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v_localDecl_671_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_677_, lean_object* v_givenName_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_677_, v_givenName_678_);
lean_dec(v_givenName_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_680_, uint8_t v_skipAuxDecl_681_, lean_object* v_auxDeclToFullName_682_, lean_object* v___x_683_, lean_object* v_givenNameView_684_, lean_object* v_as_685_, lean_object* v_i_686_){
_start:
{
lean_object* v_zero_687_; uint8_t v_isZero_688_; 
v_zero_687_ = lean_unsigned_to_nat(0u);
v_isZero_688_ = lean_nat_dec_eq(v_i_686_, v_zero_687_);
if (v_isZero_688_ == 1)
{
lean_object* v___x_689_; 
lean_dec(v_i_686_);
lean_dec_ref(v_givenNameView_684_);
lean_dec(v___x_683_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
else
{
lean_object* v_one_690_; lean_object* v_n_691_; lean_object* v___y_693_; lean_object* v___x_695_; 
v_one_690_ = lean_unsigned_to_nat(1u);
v_n_691_ = lean_nat_sub(v_i_686_, v_one_690_);
lean_dec(v_i_686_);
v___x_695_ = lean_array_fget_borrowed(v_as_685_, v_n_691_);
if (lean_obj_tag(v___x_695_) == 0)
{
v___y_693_ = v___x_695_;
goto v___jp_692_;
}
else
{
lean_object* v_val_696_; uint8_t v___x_697_; 
v_val_696_ = lean_ctor_get(v___x_695_, 0);
v___x_697_ = l_Lean_LocalDecl_isAuxDecl(v_val_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_inc(v_val_696_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_696_, v_givenName_680_);
v___y_693_ = v___x_698_;
goto v___jp_692_;
}
else
{
if (v_skipAuxDecl_681_ == 0)
{
if (v___x_697_ == 0)
{
v_i_686_ = v_n_691_;
goto _start;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l_Lean_LocalDecl_fvarId(v_val_696_);
v___x_701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_682_, v___x_700_);
lean_dec(v___x_700_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_val_702_; lean_object* v_fullDeclView_703_; lean_object* v___y_705_; lean_object* v_name_726_; lean_object* v___x_727_; 
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v_fullDeclView_703_ = l_Lean_extractMacroScopes(v_val_702_);
v_name_726_ = lean_ctor_get(v_fullDeclView_703_, 0);
lean_inc(v_name_726_);
v___x_727_ = l_Lean_privateToUserName_x3f(v_name_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_inc(v_name_726_);
v___y_705_ = v_name_726_;
goto v___jp_704_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_727_, 1);
v___y_705_ = v_val_728_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v_imported_706_; lean_object* v_ctx_707_; lean_object* v_scopes_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_imported_706_ = lean_ctor_get(v_fullDeclView_703_, 1);
v_ctx_707_ = lean_ctor_get(v_fullDeclView_703_, 2);
v_scopes_708_ = lean_ctor_get(v_fullDeclView_703_, 3);
v_isSharedCheck_724_ = !lean_is_exclusive(v_fullDeclView_703_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_fullDeclView_703_, 0);
lean_dec(v_unused_725_);
v___x_710_ = v_fullDeclView_703_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_scopes_708_);
lean_inc(v_ctx_707_);
lean_inc(v_imported_706_);
lean_dec(v_fullDeclView_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_fullDeclView_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___y_705_);
v_fullDeclView_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___y_705_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_imported_706_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_ctx_707_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_scopes_708_);
v_fullDeclView_713_ = v_reuseFailAlloc_723_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v_fullDeclName_714_; uint8_t v___x_715_; 
lean_inc_ref(v_fullDeclView_713_);
v_fullDeclName_714_ = l_Lean_MacroScopesView_review(v_fullDeclView_713_);
v___x_715_ = l_Lean_Name_isPrefixOf(v___x_683_, v_fullDeclName_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_fullDeclView_713_);
lean_inc(v___x_683_);
lean_inc_ref(v_givenNameView_684_);
lean_inc(v_val_696_);
v___x_716_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_696_, v_givenNameView_684_, v_fullDeclName_714_, v___x_683_);
lean_dec(v_fullDeclName_714_);
v___y_693_ = v___x_716_;
goto v___jp_692_;
}
else
{
lean_object* v___x_717_; lean_object* v_localDeclNameView_718_; uint8_t v___x_719_; 
lean_dec(v_fullDeclName_714_);
v___x_717_ = l_Lean_LocalDecl_userName(v_val_696_);
v_localDeclNameView_718_ = l_Lean_extractMacroScopes(v___x_717_);
v___x_719_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_718_, v_givenNameView_684_);
lean_dec_ref(v_localDeclNameView_718_);
if (v___x_719_ == 0)
{
lean_dec_ref(v_fullDeclView_713_);
v_i_686_ = v_n_691_;
goto _start;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_684_, v_fullDeclView_713_);
lean_dec_ref(v_fullDeclView_713_);
if (v___x_721_ == 0)
{
v_i_686_ = v_n_691_;
goto _start;
}
else
{
lean_inc_ref(v___x_695_);
v___y_693_ = v___x_695_;
goto v___jp_692_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_729_; 
lean_dec(v___x_701_);
lean_inc(v_val_696_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_696_, v_givenName_680_);
v___y_693_ = v___x_729_;
goto v___jp_692_;
}
}
}
else
{
v_i_686_ = v_n_691_;
goto _start;
}
}
}
v___jp_692_:
{
if (lean_obj_tag(v___y_693_) == 0)
{
v_i_686_ = v_n_691_;
goto _start;
}
else
{
lean_dec(v_n_691_);
lean_dec_ref(v_givenNameView_684_);
lean_dec(v___x_683_);
return v___y_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_731_, lean_object* v_skipAuxDecl_732_, lean_object* v_auxDeclToFullName_733_, lean_object* v___x_734_, lean_object* v_givenNameView_735_, lean_object* v_as_736_, lean_object* v_i_737_){
_start:
{
uint8_t v_skipAuxDecl_boxed_738_; lean_object* v_res_739_; 
v_skipAuxDecl_boxed_738_ = lean_unbox(v_skipAuxDecl_732_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_731_, v_skipAuxDecl_boxed_738_, v_auxDeclToFullName_733_, v___x_734_, v_givenNameView_735_, v_as_736_, v_i_737_);
lean_dec_ref(v_as_736_);
lean_dec(v_auxDeclToFullName_733_);
lean_dec(v_givenName_731_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_740_, uint8_t v_skipAuxDecl_741_, lean_object* v_auxDeclToFullName_742_, lean_object* v___x_743_, lean_object* v_givenNameView_744_, lean_object* v_as_745_, lean_object* v_i_746_){
_start:
{
lean_object* v_zero_747_; uint8_t v_isZero_748_; 
v_zero_747_ = lean_unsigned_to_nat(0u);
v_isZero_748_ = lean_nat_dec_eq(v_i_746_, v_zero_747_);
if (v_isZero_748_ == 1)
{
lean_object* v___x_749_; 
lean_dec(v_i_746_);
lean_dec_ref(v_givenNameView_744_);
lean_dec(v___x_743_);
v___x_749_ = lean_box(0);
return v___x_749_;
}
else
{
lean_object* v_one_750_; lean_object* v_n_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_one_750_ = lean_unsigned_to_nat(1u);
v_n_751_ = lean_nat_sub(v_i_746_, v_one_750_);
lean_dec(v_i_746_);
v___x_752_ = lean_array_fget_borrowed(v_as_745_, v_n_751_);
lean_inc_ref(v_givenNameView_744_);
lean_inc(v___x_743_);
v___x_753_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_740_, v_skipAuxDecl_741_, v_auxDeclToFullName_742_, v___x_743_, v_givenNameView_744_, v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
v_i_746_ = v_n_751_;
goto _start;
}
else
{
lean_dec(v_n_751_);
lean_dec_ref(v_givenNameView_744_);
lean_dec(v___x_743_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_755_, uint8_t v_skipAuxDecl_756_, lean_object* v_auxDeclToFullName_757_, lean_object* v___x_758_, lean_object* v_givenNameView_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_cs_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_cs_761_ = lean_ctor_get(v_x_760_, 0);
v___x_762_ = lean_array_get_size(v_cs_761_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_755_, v_skipAuxDecl_756_, v_auxDeclToFullName_757_, v___x_758_, v_givenNameView_759_, v_cs_761_, v___x_762_);
return v___x_763_;
}
else
{
lean_object* v_vs_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_vs_764_ = lean_ctor_get(v_x_760_, 0);
v___x_765_ = lean_array_get_size(v_vs_764_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_755_, v_skipAuxDecl_756_, v_auxDeclToFullName_757_, v___x_758_, v_givenNameView_759_, v_vs_764_, v___x_765_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_767_, lean_object* v_skipAuxDecl_768_, lean_object* v_auxDeclToFullName_769_, lean_object* v___x_770_, lean_object* v_givenNameView_771_, lean_object* v_x_772_){
_start:
{
uint8_t v_skipAuxDecl_boxed_773_; lean_object* v_res_774_; 
v_skipAuxDecl_boxed_773_ = lean_unbox(v_skipAuxDecl_768_);
v_res_774_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_767_, v_skipAuxDecl_boxed_773_, v_auxDeclToFullName_769_, v___x_770_, v_givenNameView_771_, v_x_772_);
lean_dec_ref(v_x_772_);
lean_dec(v_auxDeclToFullName_769_);
lean_dec(v_givenName_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_775_, lean_object* v_skipAuxDecl_776_, lean_object* v_auxDeclToFullName_777_, lean_object* v___x_778_, lean_object* v_givenNameView_779_, lean_object* v_as_780_, lean_object* v_i_781_){
_start:
{
uint8_t v_skipAuxDecl_boxed_782_; lean_object* v_res_783_; 
v_skipAuxDecl_boxed_782_ = lean_unbox(v_skipAuxDecl_776_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_775_, v_skipAuxDecl_boxed_782_, v_auxDeclToFullName_777_, v___x_778_, v_givenNameView_779_, v_as_780_, v_i_781_);
lean_dec_ref(v_as_780_);
lean_dec(v_auxDeclToFullName_777_);
lean_dec(v_givenName_775_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_784_, uint8_t v_skipAuxDecl_785_, lean_object* v_auxDeclToFullName_786_, lean_object* v___x_787_, lean_object* v_givenNameView_788_, lean_object* v_t_789_){
_start:
{
lean_object* v_root_790_; lean_object* v_tail_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_root_790_ = lean_ctor_get(v_t_789_, 0);
v_tail_791_ = lean_ctor_get(v_t_789_, 1);
v___x_792_ = lean_array_get_size(v_tail_791_);
lean_inc_ref(v_givenNameView_788_);
lean_inc(v___x_787_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_784_, v_skipAuxDecl_785_, v_auxDeclToFullName_786_, v___x_787_, v_givenNameView_788_, v_tail_791_, v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_784_, v_skipAuxDecl_785_, v_auxDeclToFullName_786_, v___x_787_, v_givenNameView_788_, v_root_790_);
return v___x_794_;
}
else
{
lean_dec_ref(v_givenNameView_788_);
lean_dec(v___x_787_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_795_, lean_object* v_skipAuxDecl_796_, lean_object* v_auxDeclToFullName_797_, lean_object* v___x_798_, lean_object* v_givenNameView_799_, lean_object* v_t_800_){
_start:
{
uint8_t v_skipAuxDecl_boxed_801_; lean_object* v_res_802_; 
v_skipAuxDecl_boxed_801_ = lean_unbox(v_skipAuxDecl_796_);
v_res_802_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_795_, v_skipAuxDecl_boxed_801_, v_auxDeclToFullName_797_, v___x_798_, v_givenNameView_799_, v_t_800_);
lean_dec_ref(v_t_800_);
lean_dec(v_auxDeclToFullName_797_);
lean_dec(v_givenName_795_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_803_, lean_object* v_givenName_804_, lean_object* v_as_805_, lean_object* v_i_806_){
_start:
{
lean_object* v_zero_807_; uint8_t v_isZero_808_; 
v_zero_807_ = lean_unsigned_to_nat(0u);
v_isZero_808_ = lean_nat_dec_eq(v_i_806_, v_zero_807_);
if (v_isZero_808_ == 1)
{
lean_object* v___x_809_; 
lean_dec(v_i_806_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v_one_810_; lean_object* v_n_811_; lean_object* v___y_813_; lean_object* v___x_815_; 
v_one_810_ = lean_unsigned_to_nat(1u);
v_n_811_ = lean_nat_sub(v_i_806_, v_one_810_);
lean_dec(v_i_806_);
v___x_815_ = lean_array_fget_borrowed(v_as_805_, v_n_811_);
if (lean_obj_tag(v___x_815_) == 0)
{
v___y_813_ = v___x_815_;
goto v___jp_812_;
}
else
{
lean_object* v_val_816_; uint8_t v___x_817_; 
v_val_816_ = lean_ctor_get(v___x_815_, 0);
v___x_817_ = l_Lean_LocalDecl_isAuxDecl(v_val_816_);
if (v___x_817_ == 0)
{
v___y_813_ = v_localDecl_x3f_803_;
goto v___jp_812_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = l_Lean_LocalDecl_userName(v_val_816_);
v___x_819_ = lean_name_eq(v___x_818_, v_givenName_804_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
v_i_806_ = v_n_811_;
goto _start;
}
else
{
v___y_813_ = v___x_815_;
goto v___jp_812_;
}
}
}
v___jp_812_:
{
if (lean_obj_tag(v___y_813_) == 0)
{
v_i_806_ = v_n_811_;
goto _start;
}
else
{
lean_dec(v_n_811_);
lean_inc_ref(v___y_813_);
return v___y_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_821_, lean_object* v_givenName_822_, lean_object* v_as_823_, lean_object* v_i_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_821_, v_givenName_822_, v_as_823_, v_i_824_);
lean_dec_ref(v_as_823_);
lean_dec(v_givenName_822_);
lean_dec(v_localDecl_x3f_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_826_, lean_object* v_givenName_827_, lean_object* v_as_828_, lean_object* v_i_829_){
_start:
{
lean_object* v_zero_830_; uint8_t v_isZero_831_; 
v_zero_830_ = lean_unsigned_to_nat(0u);
v_isZero_831_ = lean_nat_dec_eq(v_i_829_, v_zero_830_);
if (v_isZero_831_ == 1)
{
lean_object* v___x_832_; 
lean_dec(v_i_829_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v_one_833_; lean_object* v_n_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_one_833_ = lean_unsigned_to_nat(1u);
v_n_834_ = lean_nat_sub(v_i_829_, v_one_833_);
lean_dec(v_i_829_);
v___x_835_ = lean_array_fget_borrowed(v_as_828_, v_n_834_);
v___x_836_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_826_, v_givenName_827_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
v_i_829_ = v_n_834_;
goto _start;
}
else
{
lean_dec(v_n_834_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_838_, lean_object* v_givenName_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_cs_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_cs_841_ = lean_ctor_get(v_x_840_, 0);
v___x_842_ = lean_array_get_size(v_cs_841_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_838_, v_givenName_839_, v_cs_841_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_vs_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_vs_844_ = lean_ctor_get(v_x_840_, 0);
v___x_845_ = lean_array_get_size(v_vs_844_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_838_, v_givenName_839_, v_vs_844_, v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_847_, lean_object* v_givenName_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_847_, v_givenName_848_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec(v_givenName_848_);
lean_dec(v_localDecl_x3f_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_851_, lean_object* v_givenName_852_, lean_object* v_as_853_, lean_object* v_i_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_851_, v_givenName_852_, v_as_853_, v_i_854_);
lean_dec_ref(v_as_853_);
lean_dec(v_givenName_852_);
lean_dec(v_localDecl_x3f_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_856_, lean_object* v_givenName_857_, lean_object* v_t_858_){
_start:
{
lean_object* v_root_859_; lean_object* v_tail_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_root_859_ = lean_ctor_get(v_t_858_, 0);
v_tail_860_ = lean_ctor_get(v_t_858_, 1);
v___x_861_ = lean_array_get_size(v_tail_860_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_856_, v_givenName_857_, v_tail_860_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_856_, v_givenName_857_, v_root_859_);
return v___x_863_;
}
else
{
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_864_, lean_object* v_givenName_865_, lean_object* v_t_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_864_, v_givenName_865_, v_t_866_);
lean_dec_ref(v_t_866_);
lean_dec(v_givenName_865_);
lean_dec(v_localDecl_x3f_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_868_, lean_object* v_currNamespace_869_, lean_object* v_decls_870_, lean_object* v_givenNameView_871_, uint8_t v_skipAuxDecl_872_){
_start:
{
lean_object* v_givenName_873_; lean_object* v_localDecl_x3f_874_; 
lean_inc_ref(v_givenNameView_871_);
v_givenName_873_ = l_Lean_MacroScopesView_review(v_givenNameView_871_);
v_localDecl_x3f_874_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_873_, v_skipAuxDecl_872_, v_auxDeclToFullName_868_, v_currNamespace_869_, v_givenNameView_871_, v_decls_870_);
if (lean_obj_tag(v_localDecl_x3f_874_) == 0)
{
if (v_skipAuxDecl_872_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_874_, v_givenName_873_, v_decls_870_);
lean_dec(v_givenName_873_);
return v___x_875_;
}
else
{
lean_dec(v_givenName_873_);
return v_localDecl_x3f_874_;
}
}
else
{
lean_dec(v_givenName_873_);
return v_localDecl_x3f_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_876_, lean_object* v_currNamespace_877_, lean_object* v_decls_878_, lean_object* v_givenNameView_879_, lean_object* v_skipAuxDecl_880_){
_start:
{
uint8_t v_skipAuxDecl_boxed_881_; lean_object* v_res_882_; 
v_skipAuxDecl_boxed_881_ = lean_unbox(v_skipAuxDecl_880_);
v_res_882_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_876_, v_currNamespace_877_, v_decls_878_, v_givenNameView_879_, v_skipAuxDecl_boxed_881_);
lean_dec_ref(v_decls_878_);
lean_dec(v_auxDeclToFullName_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_lctx_889_; lean_object* v_toCold_890_; lean_object* v_decls_891_; lean_object* v_auxDeclToFullName_892_; lean_object* v_currNamespace_893_; lean_object* v_view_894_; lean_object* v_name_895_; lean_object* v_findLocalDecl_x3f_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; 
v_lctx_889_ = lean_ctor_get(v___y_884_, 2);
v_toCold_890_ = lean_ctor_get(v___y_886_, 0);
v_decls_891_ = lean_ctor_get(v_lctx_889_, 1);
v_auxDeclToFullName_892_ = lean_ctor_get(v_lctx_889_, 2);
v_currNamespace_893_ = lean_ctor_get(v_toCold_890_, 4);
v_view_894_ = l_Lean_extractMacroScopes(v_n_883_);
v_name_895_ = lean_ctor_get(v_view_894_, 0);
lean_inc(v_name_895_);
lean_inc_ref(v_decls_891_);
lean_inc(v_currNamespace_893_);
lean_inc(v_auxDeclToFullName_892_);
v_findLocalDecl_x3f_896_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_896_, 0, v_auxDeclToFullName_892_);
lean_closure_set(v_findLocalDecl_x3f_896_, 1, v_currNamespace_893_);
lean_closure_set(v_findLocalDecl_x3f_896_, 2, v_decls_891_);
v___x_897_ = lean_box(0);
v___x_898_ = 0;
v___x_899_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_894_, v_findLocalDecl_x3f_896_, v_name_895_, v___x_897_, v___x_898_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec_ref(v_view_894_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_907_, lean_object* v_n_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_928_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_928_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 0)
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_919_ = 1;
v___x_920_ = lean_box(v___x_919_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_926_; 
lean_dec_ref_known(v_a_915_, 1);
v___x_924_ = lean_box(v___x_907_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_924_);
v___x_926_ = v___x_917_;
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
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_914_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_914_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_937_, lean_object* v_n_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_44343__boxed_944_; lean_object* v_res_945_; 
v___x_44343__boxed_944_ = lean_unbox(v___x_937_);
v_res_945_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(v___x_44343__boxed_944_, v_n_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_946_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_963_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_961_);
v___x_964_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_963_, v_opt_960_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_968_, v___y_969_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_opt_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_974_, lean_object* v_msgData_975_, uint8_t v_severity_976_, uint8_t v_isSilent_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_a_984_; uint8_t v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v_toCold_995_; lean_object* v___y_996_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; uint8_t v___y_1027_; lean_object* v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; uint8_t v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1060_; uint8_t v___y_1061_; uint8_t v___y_1062_; uint8_t v___x_1073_; uint8_t v___y_1075_; uint8_t v___y_1076_; uint8_t v___y_1077_; uint8_t v___y_1079_; uint8_t v___x_1087_; 
v___x_1073_ = 2;
v___x_1087_ = l_Lean_instBEqMessageSeverity_beq(v_severity_976_, v___x_1073_);
if (v___x_1087_ == 0)
{
v___y_1079_ = v___x_1087_;
goto v___jp_1078_;
}
else
{
uint8_t v___x_1088_; 
lean_inc_ref(v_msgData_975_);
v___x_1088_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_975_);
v___y_1079_ = v___x_1088_;
goto v___jp_1078_;
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_a_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
v___jp_987_:
{
lean_object* v_currNamespace_997_; lean_object* v_openDecls_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_env_1003_; lean_object* v_nextMacroScope_1004_; lean_object* v_ngen_1005_; lean_object* v_auxDeclNGen_1006_; lean_object* v_traceState_1007_; lean_object* v_cache_1008_; lean_object* v_recordedDeps_1009_; lean_object* v_messages_1010_; lean_object* v_infoState_1011_; lean_object* v_snapshotTasks_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1022_; 
v_currNamespace_997_ = lean_ctor_get(v_toCold_995_, 4);
v_openDecls_998_ = lean_ctor_get(v_toCold_995_, 5);
lean_inc(v_openDecls_998_);
lean_inc(v_currNamespace_997_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_currNamespace_997_);
lean_ctor_set(v___x_999_, 1, v_openDecls_998_);
v___x_1000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___y_994_);
lean_inc_ref(v___y_989_);
lean_inc_ref(v___y_991_);
v___x_1001_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1001_, 0, v___y_991_);
lean_ctor_set(v___x_1001_, 1, v___y_993_);
lean_ctor_set(v___x_1001_, 2, v___y_990_);
lean_ctor_set(v___x_1001_, 3, v___y_989_);
lean_ctor_set(v___x_1001_, 4, v___x_1000_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*5, v___y_992_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*5 + 1, v___y_988_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*5 + 2, v_isSilent_977_);
v___x_1002_ = lean_st_ref_take(v___y_996_);
v_env_1003_ = lean_ctor_get(v___x_1002_, 0);
v_nextMacroScope_1004_ = lean_ctor_get(v___x_1002_, 1);
v_ngen_1005_ = lean_ctor_get(v___x_1002_, 2);
v_auxDeclNGen_1006_ = lean_ctor_get(v___x_1002_, 3);
v_traceState_1007_ = lean_ctor_get(v___x_1002_, 4);
v_cache_1008_ = lean_ctor_get(v___x_1002_, 5);
v_recordedDeps_1009_ = lean_ctor_get(v___x_1002_, 6);
v_messages_1010_ = lean_ctor_get(v___x_1002_, 7);
v_infoState_1011_ = lean_ctor_get(v___x_1002_, 8);
v_snapshotTasks_1012_ = lean_ctor_get(v___x_1002_, 9);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snapshotTasks_1012_);
lean_inc(v_infoState_1011_);
lean_inc(v_messages_1010_);
lean_inc(v_recordedDeps_1009_);
lean_inc(v_cache_1008_);
lean_inc(v_traceState_1007_);
lean_inc(v_auxDeclNGen_1006_);
lean_inc(v_ngen_1005_);
lean_inc(v_nextMacroScope_1004_);
lean_inc(v_env_1003_);
lean_dec(v___x_1002_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = l_Lean_MessageLog_add(v___x_1001_, v_messages_1010_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 7, v___x_1017_);
v___x_1019_ = v___x_1014_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_env_1003_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_nextMacroScope_1004_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_ngen_1005_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_auxDeclNGen_1006_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_traceState_1007_);
lean_ctor_set(v_reuseFailAlloc_1021_, 5, v_cache_1008_);
lean_ctor_set(v_reuseFailAlloc_1021_, 6, v_recordedDeps_1009_);
lean_ctor_set(v_reuseFailAlloc_1021_, 7, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1021_, 8, v_infoState_1011_);
lean_ctor_set(v_reuseFailAlloc_1021_, 9, v_snapshotTasks_1012_);
v___x_1019_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_st_ref_put(v___y_996_, v___x_1019_);
v_a_984_ = v___x_1016_;
goto v___jp_983_;
}
}
}
v___jp_1023_:
{
lean_object* v_fileName_1032_; lean_object* v_fileMap_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1048_; 
v_fileName_1032_ = lean_ctor_get(v___y_1030_, 0);
v_fileMap_1033_ = lean_ctor_get(v___y_1030_, 1);
v___x_1034_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_975_);
v___x_1035_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1034_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1048_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_inc_ref_n(v_fileMap_1033_, 2);
v___x_1040_ = l_Lean_FileMap_toPosition(v_fileMap_1033_, v___y_1028_);
lean_dec(v___y_1028_);
v___x_1041_ = l_Lean_FileMap_toPosition(v_fileMap_1033_, v___y_1031_);
lean_dec(v___y_1031_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1043_ = v___x_1038_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1026_ == 0)
{
lean_dec_ref(v___y_1024_);
v___y_988_ = v___y_1027_;
v___y_989_ = v___x_1044_;
v___y_990_ = v___x_1043_;
v___y_991_ = v_fileName_1032_;
v___y_992_ = v___y_1029_;
v___y_993_ = v___x_1040_;
v___y_994_ = v_a_1036_;
v_toCold_995_ = v___y_1025_;
v___y_996_ = v___y_981_;
goto v___jp_987_;
}
else
{
uint8_t v___x_1045_; 
lean_inc(v_a_1036_);
v___x_1045_ = l_Lean_MessageData_hasTag(v___y_1024_, v_a_1036_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec_ref(v___x_1043_);
lean_dec_ref(v___x_1040_);
lean_dec(v_a_1036_);
v___x_1046_ = lean_box(0);
v_a_984_ = v___x_1046_;
goto v___jp_983_;
}
else
{
v___y_988_ = v___y_1027_;
v___y_989_ = v___x_1044_;
v___y_990_ = v___x_1043_;
v___y_991_ = v_fileName_1032_;
v___y_992_ = v___y_1029_;
v___y_993_ = v___x_1040_;
v___y_994_ = v_a_1036_;
v_toCold_995_ = v___y_1025_;
v___y_996_ = v___y_981_;
goto v___jp_987_;
}
}
}
}
}
v___jp_1049_:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Syntax_getTailPos_x3f(v___y_1053_, v___y_1055_);
lean_dec(v___y_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_inc(v___y_1056_);
v___y_1024_ = v___y_1051_;
v___y_1025_ = v___y_1052_;
v___y_1026_ = v___y_1050_;
v___y_1027_ = v___y_1054_;
v___y_1028_ = v___y_1056_;
v___y_1029_ = v___y_1055_;
v___y_1030_ = v___y_1052_;
v___y_1031_ = v___y_1056_;
goto v___jp_1023_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___y_1024_ = v___y_1051_;
v___y_1025_ = v___y_1052_;
v___y_1026_ = v___y_1050_;
v___y_1027_ = v___y_1054_;
v___y_1028_ = v___y_1056_;
v___y_1029_ = v___y_1055_;
v___y_1030_ = v___y_1052_;
v___y_1031_ = v_val_1058_;
goto v___jp_1023_;
}
}
v___jp_1059_:
{
lean_object* v_toCold_1063_; lean_object* v_ref_1064_; uint8_t v_suppressElabErrors_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___f_1068_; lean_object* v_ref_1069_; lean_object* v___x_1070_; 
v_toCold_1063_ = lean_ctor_get(v___y_980_, 0);
v_ref_1064_ = lean_ctor_get(v___y_980_, 2);
v_suppressElabErrors_1065_ = lean_ctor_get_uint8(v___y_980_, sizeof(void*)*3 + 2);
v___x_1066_ = lean_box(v_suppressElabErrors_1065_);
v___x_1067_ = lean_box(v___y_1060_);
v___f_1068_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1068_, 0, v___x_1066_);
lean_closure_set(v___f_1068_, 1, v___x_1067_);
v_ref_1069_ = l_Lean_replaceRef(v_ref_974_, v_ref_1064_);
v___x_1070_ = l_Lean_Syntax_getPos_x3f(v_ref_1069_, v___y_1061_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___y_1050_ = v_suppressElabErrors_1065_;
v___y_1051_ = v___f_1068_;
v___y_1052_ = v_toCold_1063_;
v___y_1053_ = v_ref_1069_;
v___y_1054_ = v___y_1062_;
v___y_1055_ = v___y_1061_;
v___y_1056_ = v___x_1071_;
goto v___jp_1049_;
}
else
{
lean_object* v_val_1072_; 
v_val_1072_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1070_, 1);
v___y_1050_ = v_suppressElabErrors_1065_;
v___y_1051_ = v___f_1068_;
v___y_1052_ = v_toCold_1063_;
v___y_1053_ = v_ref_1069_;
v___y_1054_ = v___y_1062_;
v___y_1055_ = v___y_1061_;
v___y_1056_ = v_val_1072_;
goto v___jp_1049_;
}
}
v___jp_1074_:
{
if (v___y_1077_ == 0)
{
v___y_1060_ = v___y_1075_;
v___y_1061_ = v___y_1076_;
v___y_1062_ = v_severity_976_;
goto v___jp_1059_;
}
else
{
v___y_1060_ = v___y_1075_;
v___y_1061_ = v___y_1076_;
v___y_1062_ = v___x_1073_;
goto v___jp_1059_;
}
}
v___jp_1078_:
{
if (v___y_1079_ == 0)
{
uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = 1;
v___x_1081_ = l_Lean_instBEqMessageSeverity_beq(v_severity_976_, v___x_1080_);
if (v___x_1081_ == 0)
{
v___y_1075_ = v___y_1079_;
v___y_1076_ = v___y_1079_;
v___y_1077_ = v___x_1081_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_980_);
v___x_1083_ = l_Lean_warningAsError;
v___x_1084_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_1082_, v___x_1083_);
lean_dec_ref(v___x_1082_);
v___y_1075_ = v___y_1079_;
v___y_1076_ = v___y_1079_;
v___y_1077_ = v___x_1084_;
goto v___jp_1074_;
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v_msgData_975_);
v___x_1085_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_1089_, lean_object* v_msgData_1090_, lean_object* v_severity_1091_, lean_object* v_isSilent_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_severity_boxed_1098_; uint8_t v_isSilent_boxed_1099_; lean_object* v_res_1100_; 
v_severity_boxed_1098_ = lean_unbox(v_severity_1091_);
v_isSilent_boxed_1099_ = lean_unbox(v_isSilent_1092_);
v_res_1100_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1089_, v_msgData_1090_, v_severity_boxed_1098_, v_isSilent_boxed_1099_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v_ref_1089_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_1101_, uint8_t v_severity_1102_, uint8_t v_isSilent_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_ref_1109_; lean_object* v___x_1110_; 
v_ref_1109_ = lean_ctor_get(v___y_1106_, 2);
v___x_1110_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1109_, v_msgData_1101_, v_severity_1102_, v_isSilent_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_1111_, lean_object* v_severity_1112_, lean_object* v_isSilent_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_severity_boxed_1119_; uint8_t v_isSilent_boxed_1120_; lean_object* v_res_1121_; 
v_severity_boxed_1119_ = lean_unbox(v_severity_1112_);
v_isSilent_boxed_1120_ = lean_unbox(v_isSilent_1113_);
v_res_1121_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1111_, v_severity_boxed_1119_, v_isSilent_boxed_1120_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = 1;
v___x_1129_ = 0;
v___x_1130_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1122_, v___x_1128_, v___x_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1168_; 
v___x_1144_ = lean_st_ref_get(v___y_1142_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1146_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1147_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_1146_, v___y_1141_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v_isExporting_1157_; 
v_isExporting_1157_ = lean_ctor_get_uint8(v_env_1145_, sizeof(void*)*13);
lean_dec_ref(v_env_1145_);
if (v_isExporting_1157_ == 0)
{
lean_dec(v_a_1148_);
lean_dec(v_id_1138_);
goto v___jp_1152_;
}
else
{
lean_object* v_val_1158_; uint8_t v___x_1159_; 
v_val_1158_ = lean_ctor_get(v_a_1148_, 0);
lean_inc(v_val_1158_);
lean_dec(v_a_1148_);
v___x_1159_ = l_Lean_isPrivateName(v_id_1138_);
if (v___x_1159_ == 0)
{
lean_dec(v_val_1158_);
lean_dec(v_id_1138_);
goto v___jp_1152_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_unbox(v_val_1158_);
lean_dec(v_val_1158_);
if (v___x_1160_ == 0)
{
lean_dec(v_id_1138_);
goto v___jp_1152_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_del_object(v___x_1150_);
v___x_1161_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_1162_ = 0;
v___x_1163_ = l_Lean_MessageData_ofConstName(v_id_1138_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_1166_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1167_;
}
}
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_1176_, uint8_t v_enableLog_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_toCold_1184_; lean_object* v_env_1185_; lean_object* v_currNamespace_1186_; lean_object* v_openDecls_1187_; lean_object* v___x_1188_; lean_object* v_res_1189_; lean_object* v___x_1193_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_toCold_1184_ = lean_ctor_get(v___y_1180_, 0);
v_env_1185_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_env_1185_);
lean_dec(v___x_1183_);
v_currNamespace_1186_ = lean_ctor_get(v_toCold_1184_, 4);
v_openDecls_1187_ = lean_ctor_get(v_toCold_1184_, 5);
v___x_1188_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1180_);
lean_inc(v_openDecls_1187_);
lean_inc(v_currNamespace_1186_);
v_res_1189_ = l_Lean_ResolveName_resolveGlobalName(v_env_1185_, v___x_1188_, v_currNamespace_1186_, v_openDecls_1187_, v_id_1176_);
lean_dec_ref(v___x_1188_);
v___x_1193_ = lean_st_ref_get(v___y_1181_);
if (v_enableLog_1177_ == 0)
{
lean_dec(v___x_1193_);
goto v___jp_1190_;
}
else
{
lean_object* v_env_1194_; uint8_t v_isExporting_1195_; 
v_env_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_env_1194_);
lean_dec(v___x_1193_);
v_isExporting_1195_ = lean_ctor_get_uint8(v_env_1194_, sizeof(void*)*13);
lean_dec_ref(v_env_1194_);
if (v_isExporting_1195_ == 0)
{
goto v___jp_1190_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1189_);
if (lean_obj_tag(v___x_1196_) == 1)
{
lean_object* v_val_1197_; lean_object* v_fst_1198_; lean_object* v___x_1199_; 
v_val_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_val_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v_fst_1198_ = lean_ctor_get(v_val_1197_, 0);
lean_inc(v_fst_1198_);
lean_dec(v_val_1197_);
v___x_1199_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_1198_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
if (lean_obj_tag(v_a_1200_) == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec(v_res_1189_);
v___x_1204_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_dec_ref_known(v_a_1200_, 1);
lean_del_object(v___x_1202_);
goto v___jp_1190_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_res_1189_);
v_a_1209_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1199_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1199_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_dec(v___x_1196_);
goto v___jp_1190_;
}
}
}
v___jp_1190_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_res_1189_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_1217_, lean_object* v_enableLog_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_enableLog_boxed_1224_; lean_object* v_res_1225_; 
v_enableLog_boxed_1224_ = lean_unbox(v_enableLog_1218_);
v_res_1225_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_1217_, v_enableLog_boxed_1224_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_1230_, lean_object* v_filter_1231_, lean_object* v_view_x3f_1232_, lean_object* v_n_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1309_; 
if (lean_obj_tag(v_view_x3f_1232_) == 1)
{
lean_object* v_val_1336_; lean_object* v_imported_1337_; lean_object* v_ctx_1338_; lean_object* v_scopes_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_val_1336_ = lean_ctor_get(v_view_x3f_1232_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_view_x3f_1232_, 1);
v_imported_1337_ = lean_ctor_get(v_val_1336_, 1);
v_ctx_1338_ = lean_ctor_get(v_val_1336_, 2);
v_scopes_1339_ = lean_ctor_get(v_val_1336_, 3);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_val_1336_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_val_1336_, 0);
lean_dec(v_unused_1348_);
v___x_1341_ = v_val_1336_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_scopes_1339_);
lean_inc(v_ctx_1338_);
lean_inc(v_imported_1337_);
lean_dec(v_val_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_n_1233_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_n_1233_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_imported_1337_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_ctx_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_scopes_1339_);
v___x_1344_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_MacroScopesView_review(v___x_1344_);
v___y_1309_ = v___x_1345_;
goto v___jp_1308_;
}
}
}
else
{
lean_dec(v_view_x3f_1232_);
v___y_1309_ = v_n_1233_;
goto v___jp_1308_;
}
v___jp_1239_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
v___jp_1242_:
{
lean_object* v___x_1245_; 
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
v___x_1245_ = lean_apply_5(v___y_1244_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, lean_box(0));
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1265_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
lean_dec(v___y_1243_);
v___x_1250_ = lean_box(0);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1263_; 
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_a_1246_, 0);
lean_dec(v_unused_1264_);
v___x_1255_ = v_a_1246_;
v_isShared_1256_ = v_isSharedCheck_1263_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v_a_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1263_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___y_1243_);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___y_1243_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1258_);
v___x_1260_ = v___x_1248_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v___y_1243_);
v_a_1266_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1245_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1245_);
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
v___jp_1274_:
{
lean_object* v___x_1277_; 
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
v___x_1277_ = lean_apply_5(v___y_1276_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, lean_box(0));
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1299_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1299_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1299_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
if (lean_obj_tag(v_a_1278_) == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_dec(v___y_1275_);
lean_dec_ref(v_filter_1231_);
v___x_1282_ = lean_box(0);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v_a_1278_, 1);
lean_del_object(v___x_1280_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1275_);
v___x_1286_ = lean_apply_6(v_filter_1231_, v___y_1275_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, lean_box(0));
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___f_1289_; 
v___f_1289_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1243_ = v___y_1275_;
v___y_1244_ = v___f_1289_;
goto v___jp_1242_;
}
else
{
lean_object* v___f_1290_; 
v___f_1290_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1243_ = v___y_1275_;
v___y_1244_ = v___f_1290_;
goto v___jp_1242_;
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v___y_1275_);
v_a_1291_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1286_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1286_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v___y_1275_);
lean_dec_ref(v_filter_1231_);
v_a_1300_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1277_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1277_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
v___jp_1308_:
{
uint8_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = 0;
lean_inc(v___y_1309_);
v___x_1311_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_1309_, v___x_1310_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1327_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
if (lean_obj_tag(v_a_1312_) == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v___y_1309_);
lean_dec_ref(v_filter_1231_);
v___x_1316_ = lean_box(0);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v_val_1320_; 
lean_del_object(v___x_1314_);
v_val_1320_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v_a_1312_, 1);
if (lean_obj_tag(v_val_1320_) == 1)
{
lean_object* v_head_1321_; lean_object* v_tail_1322_; 
v_head_1321_ = lean_ctor_get(v_val_1320_, 0);
lean_inc(v_head_1321_);
v_tail_1322_ = lean_ctor_get(v_val_1320_, 1);
lean_inc(v_tail_1322_);
lean_dec_ref_known(v_val_1320_, 2);
if (lean_obj_tag(v_tail_1322_) == 0)
{
lean_object* v_fst_1323_; uint8_t v___x_1324_; 
v_fst_1323_ = lean_ctor_get(v_head_1321_, 0);
lean_inc(v_fst_1323_);
lean_dec(v_head_1321_);
v___x_1324_ = lean_name_eq(v_fst_1323_, v_n_u2080_1230_);
lean_dec(v_fst_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___f_1325_; 
v___f_1325_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1275_ = v___y_1309_;
v___y_1276_ = v___f_1325_;
goto v___jp_1274_;
}
else
{
lean_object* v___f_1326_; 
v___f_1326_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1275_ = v___y_1309_;
v___y_1276_ = v___f_1326_;
goto v___jp_1274_;
}
}
else
{
lean_dec(v_tail_1322_);
lean_dec(v_head_1321_);
lean_dec(v___y_1309_);
lean_dec_ref(v_filter_1231_);
goto v___jp_1239_;
}
}
else
{
lean_dec(v_val_1320_);
lean_dec(v___y_1309_);
lean_dec_ref(v_filter_1231_);
goto v___jp_1239_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v___y_1309_);
lean_dec_ref(v_filter_1231_);
v_a_1328_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1311_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1311_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_1349_, lean_object* v_filter_1350_, lean_object* v_view_x3f_1351_, lean_object* v_n_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1349_, v_filter_1350_, v_view_x3f_1351_, v_n_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v_n_u2080_1349_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_1359_, lean_object* v_filter_1360_, lean_object* v_view_x3f_1361_, lean_object* v_as_x27_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
if (lean_obj_tag(v_as_x27_1362_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_view_x3f_1361_);
lean_dec_ref(v_filter_1360_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_b_1363_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
else
{
lean_object* v_head_1371_; lean_object* v_tail_1372_; lean_object* v_snd_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1411_; 
v_head_1371_ = lean_ctor_get(v_as_x27_1362_, 0);
v_tail_1372_ = lean_ctor_get(v_as_x27_1362_, 1);
v_snd_1373_ = lean_ctor_get(v_b_1363_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1412_);
v___x_1375_ = v_b_1363_;
v_isShared_1376_ = v_isSharedCheck_1411_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snd_1373_);
lean_dec(v_b_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1411_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = l_Lean_Name_appendCore(v_head_1371_, v_snd_1373_);
lean_inc(v___x_1378_);
lean_inc(v_view_x3f_1361_);
lean_inc_ref(v_filter_1360_);
v___x_1379_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1359_, v_filter_1360_, v_view_x3f_1361_, v___x_1378_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1402_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1402_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1402_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 0)
{
lean_object* v___x_1385_; 
lean_del_object(v___x_1382_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1378_);
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1385_ = v___x_1375_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1378_);
v___x_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v_as_x27_1362_ = v_tail_1372_;
v_b_1363_ = v___x_1385_;
goto _start;
}
}
else
{
lean_object* v___x_1389_; 
lean_dec(v_view_x3f_1361_);
lean_dec_ref(v_filter_1360_);
lean_inc_ref(v_a_1380_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1378_);
lean_ctor_set(v___x_1375_, 0, v_a_1380_);
v___x_1389_ = v___x_1375_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1380_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1378_);
v___x_1389_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1399_; 
v_isSharedCheck_1399_ = !lean_is_exclusive(v_a_1380_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_a_1380_, 0);
lean_dec(v_unused_1400_);
v___x_1391_ = v_a_1380_;
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_a_1380_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1389_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1394_);
v___x_1396_ = v___x_1382_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v___x_1378_);
lean_del_object(v___x_1375_);
lean_dec(v_view_x3f_1361_);
lean_dec_ref(v_filter_1360_);
v_a_1403_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1379_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1379_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_1413_, lean_object* v_filter_1414_, lean_object* v_view_x3f_1415_, lean_object* v_as_x27_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1413_, v_filter_1414_, v_view_x3f_1415_, v_as_x27_1416_, v_b_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v_as_x27_1416_);
lean_dec(v_n_u2080_1413_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_1427_, lean_object* v_filter_1428_, lean_object* v_view_x3f_1429_, lean_object* v_n_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___y_1437_; uint8_t v___x_1478_; 
v___x_1478_ = l_Lean_Name_hasMacroScopes(v_n_1430_);
if (v___x_1478_ == 0)
{
lean_object* v___f_1479_; 
v___f_1479_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1437_ = v___f_1479_;
goto v___jp_1436_;
}
else
{
lean_object* v___f_1480_; 
v___f_1480_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1437_ = v___f_1480_;
goto v___jp_1436_;
}
v___jp_1436_:
{
lean_object* v___x_1438_; 
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
v___x_1438_ = lean_apply_5(v___y_1437_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1469_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_a_1439_) == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_dec(v_n_1430_);
lean_dec(v_view_x3f_1429_);
lean_dec_ref(v_filter_1428_);
v___x_1443_ = lean_box(0);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref_known(v_a_1439_, 1);
lean_del_object(v___x_1441_);
v___x_1447_ = l_Lean_privateToUserName(v_n_1430_);
v___x_1448_ = l_Lean_Name_componentsRev(v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_1450_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1427_, v_filter_1428_, v_view_x3f_1429_, v___x_1448_, v___x_1449_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___x_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_val_1455_; lean_object* v_fst_1456_; lean_object* v___x_1458_; 
v_val_1455_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_val_1455_);
lean_dec(v_a_1451_);
v_fst_1456_ = lean_ctor_get(v_val_1455_, 0);
lean_inc(v_fst_1456_);
lean_dec(v_val_1455_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v_fst_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_fst_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1450_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1450_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_n_1430_);
lean_dec(v_view_x3f_1429_);
lean_dec_ref(v_filter_1428_);
v_a_1470_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1438_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1438_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1481_, lean_object* v_filter_1482_, lean_object* v_view_x3f_1483_, lean_object* v_n_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1481_, v_filter_1482_, v_view_x3f_1483_, v_n_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_n_u2080_1481_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1491_, lean_object* v_filter_1492_, lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_array_get_size(v_as_1493_);
v___x_1501_ = lean_nat_dec_lt(v_i_1494_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_i_1494_);
lean_dec_ref(v_filter_1492_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_array_fget_borrowed(v_as_1493_, v_i_1494_);
lean_inc(v___x_1505_);
lean_inc_ref(v_filter_1492_);
v___x_1506_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1491_, v_filter_1492_, v___x_1504_, v___x_1505_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
if (lean_obj_tag(v_a_1507_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v_i_1494_, v___x_1508_);
lean_dec(v_i_1494_);
v_i_1494_ = v___x_1509_;
goto _start;
}
else
{
lean_dec(v_i_1494_);
lean_dec_ref(v_filter_1492_);
return v___x_1506_;
}
}
else
{
lean_dec(v_i_1494_);
lean_dec_ref(v_filter_1492_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1511_, lean_object* v_filter_1512_, lean_object* v_as_1513_, lean_object* v_i_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1511_, v_filter_1512_, v_as_1513_, v_i_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec_ref(v_as_1513_);
lean_dec(v_n_u2080_1511_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1521_, lean_object* v_as_1522_, size_t v_i_1523_, size_t v_stop_1524_, lean_object* v_b_1525_){
_start:
{
lean_object* v___y_1527_; uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_eq(v_i_1523_, v_stop_1524_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1532_ = lean_array_uget_borrowed(v_as_1522_, v_i_1523_);
v___x_1533_ = l_Lean_Name_getPrefix(v___x_1532_);
v___x_1534_ = l_Lean_Name_getPrefix(v_n_u2081_1521_);
v___x_1535_ = l_Lean_Name_isPrefixOf(v___x_1533_, v___x_1534_);
lean_dec(v___x_1534_);
lean_dec(v___x_1533_);
if (v___x_1535_ == 0)
{
v___y_1527_ = v_b_1525_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1536_; 
lean_inc(v___x_1532_);
v___x_1536_ = lean_array_push(v_b_1525_, v___x_1532_);
v___y_1527_ = v___x_1536_;
goto v___jp_1526_;
}
}
else
{
return v_b_1525_;
}
v___jp_1526_:
{
size_t v___x_1528_; size_t v___x_1529_; 
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1523_, v___x_1528_);
v_i_1523_ = v___x_1529_;
v_b_1525_ = v___y_1527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1537_, lean_object* v_as_1538_, lean_object* v_i_1539_, lean_object* v_stop_1540_, lean_object* v_b_1541_){
_start:
{
size_t v_i_boxed_1542_; size_t v_stop_boxed_1543_; lean_object* v_res_1544_; 
v_i_boxed_1542_ = lean_unbox_usize(v_i_1539_);
lean_dec(v_i_1539_);
v_stop_boxed_1543_ = lean_unbox_usize(v_stop_1540_);
lean_dec(v_stop_1540_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1537_, v_as_1538_, v_i_boxed_1542_, v_stop_boxed_1543_, v_b_1541_);
lean_dec_ref(v_as_1538_);
lean_dec(v_n_u2081_1537_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1547_, uint8_t v_fullNames_1548_, uint8_t v_allowHorizAliases_1549_, lean_object* v_filter_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_view_1556_; lean_object* v_name_1557_; lean_object* v_n_u2081_1558_; 
lean_inc(v_n_u2080_1547_);
v_view_1556_ = l_Lean_extractMacroScopes(v_n_u2080_1547_);
v_name_1557_ = lean_ctor_get(v_view_1556_, 0);
lean_inc(v_name_1557_);
v_n_u2081_1558_ = l_Lean_privateToUserName(v_name_1557_);
if (v_fullNames_1548_ == 0)
{
lean_object* v___x_1559_; lean_object* v_aliases_1561_; lean_object* v_env_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1559_ = lean_st_ref_get(v___y_1554_);
v_env_1576_ = lean_ctor_get(v___x_1559_, 0);
lean_inc_ref(v_env_1576_);
lean_dec(v___x_1559_);
lean_inc(v_n_u2080_1547_);
v___x_1577_ = l_Lean_getRevAliases(v_env_1576_, v_n_u2080_1547_);
v___x_1578_ = lean_array_mk(v___x_1577_);
if (v_allowHorizAliases_1549_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_array_get_size(v___x_1578_);
v___x_1581_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1582_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1582_ == 0)
{
lean_dec_ref(v___x_1578_);
v_aliases_1561_ = v___x_1581_;
goto v___jp_1560_;
}
else
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1580_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1558_, v___x_1578_, v___x_1583_, v___x_1584_, v___x_1581_);
lean_dec_ref(v___x_1578_);
v_aliases_1561_ = v___x_1585_;
goto v___jp_1560_;
}
}
else
{
v_aliases_1561_ = v___x_1578_;
goto v___jp_1560_;
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1550_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1547_, v_filter_1550_, v_aliases_1561_, v___x_1562_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec_ref(v_aliases_1561_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
if (lean_obj_tag(v_a_1564_) == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1574_; 
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v___x_1563_, 0);
lean_dec(v_unused_1575_);
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 1);
lean_ctor_set(v___x_1566_, 0, v_view_1556_);
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_view_1556_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = l_Lean_rootNamespace;
v___x_1571_ = l_Lean_Name_append(v___x_1570_, v_n_u2081_1558_);
v___x_1572_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1547_, v_filter_1550_, v___x_1569_, v___x_1571_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v_n_u2080_1547_);
return v___x_1572_;
}
}
}
else
{
lean_dec(v_n_u2081_1558_);
lean_dec_ref(v_view_1556_);
lean_dec_ref(v_filter_1550_);
lean_dec(v_n_u2080_1547_);
return v___x_1563_;
}
}
else
{
lean_dec(v_n_u2081_1558_);
lean_dec_ref(v_view_1556_);
lean_dec_ref(v_filter_1550_);
lean_dec(v_n_u2080_1547_);
return v___x_1563_;
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_view_1556_);
lean_inc(v_n_u2081_1558_);
lean_inc_ref(v___x_1586_);
lean_inc_ref(v_filter_1550_);
v___x_1587_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1547_, v_filter_1550_, v___x_1586_, v_n_u2081_1558_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
if (lean_obj_tag(v_a_1588_) == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_rootNamespace;
v___x_1590_ = l_Lean_Name_append(v___x_1589_, v_n_u2081_1558_);
v___x_1591_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1547_, v_filter_1550_, v___x_1586_, v___x_1590_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v_n_u2080_1547_);
return v___x_1591_;
}
else
{
lean_dec_ref_known(v___x_1586_, 1);
lean_dec(v_n_u2081_1558_);
lean_dec_ref(v_filter_1550_);
lean_dec(v_n_u2080_1547_);
return v___x_1587_;
}
}
else
{
lean_dec_ref_known(v___x_1586_, 1);
lean_dec(v_n_u2081_1558_);
lean_dec_ref(v_filter_1550_);
lean_dec(v_n_u2080_1547_);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1592_, lean_object* v_fullNames_1593_, lean_object* v_allowHorizAliases_1594_, lean_object* v_filter_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_fullNames_boxed_1601_; uint8_t v_allowHorizAliases_boxed_1602_; lean_object* v_res_1603_; 
v_fullNames_boxed_1601_ = lean_unbox(v_fullNames_1593_);
v_allowHorizAliases_boxed_1602_ = lean_unbox(v_allowHorizAliases_1594_);
v_res_1603_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1592_, v_fullNames_boxed_1601_, v_allowHorizAliases_boxed_1602_, v_filter_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1607_, uint8_t v_fullNames_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v___x_1614_ = 0;
v___f_1615_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0));
v___x_1616_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1607_, v_fullNames_1608_, v___x_1614_, v___f_1615_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1617_, lean_object* v_fullNames_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v_fullNames_boxed_1624_; lean_object* v_res_1625_; 
v_fullNames_boxed_1624_ = lean_unbox(v_fullNames_1618_);
v_res_1625_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_n_u2080_1617_, v_fullNames_boxed_1624_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1629_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1630_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
lean_ctor_set(v___x_1632_, 3, v___x_1631_);
lean_ctor_set(v___x_1632_, 4, v___x_1630_);
lean_ctor_set(v___x_1632_, 5, v___x_1630_);
lean_ctor_set(v___x_1632_, 6, v___x_1630_);
lean_ctor_set(v___x_1632_, 7, v___x_1630_);
lean_ctor_set(v___x_1632_, 8, v___x_1630_);
lean_ctor_set(v___x_1632_, 9, v___x_1630_);
lean_ctor_set(v___x_1632_, 10, v___x_1630_);
lean_ctor_set(v___x_1632_, 11, v___x_1629_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_unsigned_to_nat(32u);
v___x_1634_ = lean_mk_empty_array_with_capacity(v___x_1633_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = ((size_t)5ULL);
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_unsigned_to_nat(32u);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1641_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1637_);
lean_ctor_set(v___x_1641_, 3, v___x_1637_);
lean_ctor_set_usize(v___x_1641_, 4, v___x_1636_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1642_ = lean_box(1);
v___x_1643_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1644_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1643_);
lean_ctor_set(v___x_1645_, 2, v___x_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v_toCold_1651_; lean_object* v_env_1652_; lean_object* v_options_1653_; uint8_t v___x_1654_; lean_object* v_env_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1650_ = lean_st_ref_get(v___y_1648_);
v_toCold_1651_ = lean_ctor_get(v___y_1647_, 0);
v_env_1652_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_ref(v_env_1652_);
lean_dec(v___x_1650_);
v_options_1653_ = lean_ctor_get(v_toCold_1651_, 2);
v___x_1654_ = 0;
v_env_1655_ = l_Lean_Environment_setRecordingDeps(v_env_1652_, v___x_1654_);
v___x_1656_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1653_);
v___x_1658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1658_, 0, v_env_1655_);
lean_ctor_set(v___x_1658_, 1, v___x_1656_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
lean_ctor_set(v___x_1658_, 3, v_options_1653_);
v___x_1659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_msgData_1646_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_1666_, lean_object* v_msgData_1667_, uint8_t v_severity_1668_, uint8_t v_isSilent_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v___y_1674_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v_toCold_1681_; lean_object* v___y_1682_; lean_object* v___y_1711_; lean_object* v___y_1712_; uint8_t v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; uint8_t v___y_1741_; lean_object* v___y_1742_; uint8_t v___y_1743_; lean_object* v___y_1744_; uint8_t v___y_1748_; uint8_t v___y_1749_; uint8_t v___y_1750_; uint8_t v___x_1761_; uint8_t v___y_1763_; uint8_t v___y_1764_; uint8_t v___y_1765_; uint8_t v___y_1767_; uint8_t v___x_1775_; 
v___x_1761_ = 2;
v___x_1775_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1668_, v___x_1761_);
if (v___x_1775_ == 0)
{
v___y_1767_ = v___x_1775_;
goto v___jp_1766_;
}
else
{
uint8_t v___x_1776_; 
lean_inc_ref(v_msgData_1667_);
v___x_1776_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1667_);
v___y_1767_ = v___x_1776_;
goto v___jp_1766_;
}
v___jp_1673_:
{
lean_object* v_currNamespace_1683_; lean_object* v_openDecls_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v_nextMacroScope_1690_; lean_object* v_ngen_1691_; lean_object* v_auxDeclNGen_1692_; lean_object* v_traceState_1693_; lean_object* v_cache_1694_; lean_object* v_recordedDeps_1695_; lean_object* v_messages_1696_; lean_object* v_infoState_1697_; lean_object* v_snapshotTasks_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1709_; 
v_currNamespace_1683_ = lean_ctor_get(v_toCold_1681_, 4);
v_openDecls_1684_ = lean_ctor_get(v_toCold_1681_, 5);
lean_inc(v_openDecls_1684_);
lean_inc(v_currNamespace_1683_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_currNamespace_1683_);
lean_ctor_set(v___x_1685_, 1, v_openDecls_1684_);
v___x_1686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___y_1675_);
lean_inc_ref(v___y_1680_);
lean_inc_ref(v___y_1678_);
v___x_1687_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1687_, 0, v___y_1678_);
lean_ctor_set(v___x_1687_, 1, v___y_1679_);
lean_ctor_set(v___x_1687_, 2, v___y_1677_);
lean_ctor_set(v___x_1687_, 3, v___y_1680_);
lean_ctor_set(v___x_1687_, 4, v___x_1686_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*5, v___y_1674_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*5 + 1, v___y_1676_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*5 + 2, v_isSilent_1669_);
v___x_1688_ = lean_st_ref_take(v___y_1682_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1690_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1691_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1692_ = lean_ctor_get(v___x_1688_, 3);
v_traceState_1693_ = lean_ctor_get(v___x_1688_, 4);
v_cache_1694_ = lean_ctor_get(v___x_1688_, 5);
v_recordedDeps_1695_ = lean_ctor_get(v___x_1688_, 6);
v_messages_1696_ = lean_ctor_get(v___x_1688_, 7);
v_infoState_1697_ = lean_ctor_get(v___x_1688_, 8);
v_snapshotTasks_1698_ = lean_ctor_get(v___x_1688_, 9);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1700_ = v___x_1688_;
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snapshotTasks_1698_);
lean_inc(v_infoState_1697_);
lean_inc(v_messages_1696_);
lean_inc(v_recordedDeps_1695_);
lean_inc(v_cache_1694_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1692_);
lean_inc(v_ngen_1691_);
lean_inc(v_nextMacroScope_1690_);
lean_inc(v_env_1689_);
lean_dec(v___x_1688_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Lean_MessageLog_add(v___x_1687_, v_messages_1696_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 7, v___x_1703_);
v___x_1705_ = v___x_1700_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_env_1689_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_nextMacroScope_1690_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_ngen_1691_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_auxDeclNGen_1692_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v_traceState_1693_);
lean_ctor_set(v_reuseFailAlloc_1708_, 5, v_cache_1694_);
lean_ctor_set(v_reuseFailAlloc_1708_, 6, v_recordedDeps_1695_);
lean_ctor_set(v_reuseFailAlloc_1708_, 7, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1708_, 8, v_infoState_1697_);
lean_ctor_set(v_reuseFailAlloc_1708_, 9, v_snapshotTasks_1698_);
v___x_1705_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_st_ref_put(v___y_1682_, v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1702_);
return v___x_1707_;
}
}
}
v___jp_1710_:
{
lean_object* v_fileName_1719_; lean_object* v_fileMap_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1736_; 
v_fileName_1719_ = lean_ctor_get(v___y_1716_, 0);
v_fileMap_1720_ = lean_ctor_get(v___y_1716_, 1);
v___x_1721_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1667_);
v___x_1722_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v___x_1721_, v___y_1670_, v___y_1671_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_inc_ref_n(v_fileMap_1720_, 2);
v___x_1727_ = l_Lean_FileMap_toPosition(v_fileMap_1720_, v___y_1714_);
lean_dec(v___y_1714_);
v___x_1728_ = l_Lean_FileMap_toPosition(v_fileMap_1720_, v___y_1718_);
lean_dec(v___y_1718_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1717_ == 0)
{
lean_del_object(v___x_1725_);
lean_dec_ref(v___y_1711_);
v___y_1674_ = v___y_1713_;
v___y_1675_ = v_a_1723_;
v___y_1676_ = v___y_1715_;
v___y_1677_ = v___x_1729_;
v___y_1678_ = v_fileName_1719_;
v___y_1679_ = v___x_1727_;
v___y_1680_ = v___x_1730_;
v_toCold_1681_ = v___y_1712_;
v___y_1682_ = v___y_1671_;
goto v___jp_1673_;
}
else
{
uint8_t v___x_1731_; 
lean_inc(v_a_1723_);
v___x_1731_ = l_Lean_MessageData_hasTag(v___y_1711_, v_a_1723_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1729_, 1);
lean_dec_ref(v___x_1727_);
lean_dec(v_a_1723_);
v___x_1732_ = lean_box(0);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1732_);
v___x_1734_ = v___x_1725_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_del_object(v___x_1725_);
v___y_1674_ = v___y_1713_;
v___y_1675_ = v_a_1723_;
v___y_1676_ = v___y_1715_;
v___y_1677_ = v___x_1729_;
v___y_1678_ = v_fileName_1719_;
v___y_1679_ = v___x_1727_;
v___y_1680_ = v___x_1730_;
v_toCold_1681_ = v___y_1712_;
v___y_1682_ = v___y_1671_;
goto v___jp_1673_;
}
}
}
}
v___jp_1737_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Syntax_getTailPos_x3f(v___y_1742_, v___y_1741_);
lean_dec(v___y_1742_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_inc(v___y_1744_);
v___y_1711_ = v___y_1738_;
v___y_1712_ = v___y_1739_;
v___y_1713_ = v___y_1741_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1743_;
v___y_1716_ = v___y_1739_;
v___y_1717_ = v___y_1740_;
v___y_1718_ = v___y_1744_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1746_; 
v_val_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___y_1711_ = v___y_1738_;
v___y_1712_ = v___y_1739_;
v___y_1713_ = v___y_1741_;
v___y_1714_ = v___y_1744_;
v___y_1715_ = v___y_1743_;
v___y_1716_ = v___y_1739_;
v___y_1717_ = v___y_1740_;
v___y_1718_ = v_val_1746_;
goto v___jp_1710_;
}
}
v___jp_1747_:
{
lean_object* v_toCold_1751_; lean_object* v_ref_1752_; uint8_t v_suppressElabErrors_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v_ref_1757_; lean_object* v___x_1758_; 
v_toCold_1751_ = lean_ctor_get(v___y_1670_, 0);
v_ref_1752_ = lean_ctor_get(v___y_1670_, 2);
v_suppressElabErrors_1753_ = lean_ctor_get_uint8(v___y_1670_, sizeof(void*)*3 + 2);
v___x_1754_ = lean_box(v_suppressElabErrors_1753_);
v___x_1755_ = lean_box(v___y_1748_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1756_, 0, v___x_1754_);
lean_closure_set(v___f_1756_, 1, v___x_1755_);
v_ref_1757_ = l_Lean_replaceRef(v_ref_1666_, v_ref_1752_);
v___x_1758_ = l_Lean_Syntax_getPos_x3f(v_ref_1757_, v___y_1749_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_unsigned_to_nat(0u);
v___y_1738_ = v___f_1756_;
v___y_1739_ = v_toCold_1751_;
v___y_1740_ = v_suppressElabErrors_1753_;
v___y_1741_ = v___y_1749_;
v___y_1742_ = v_ref_1757_;
v___y_1743_ = v___y_1750_;
v___y_1744_ = v___x_1759_;
goto v___jp_1737_;
}
else
{
lean_object* v_val_1760_; 
v_val_1760_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v___x_1758_, 1);
v___y_1738_ = v___f_1756_;
v___y_1739_ = v_toCold_1751_;
v___y_1740_ = v_suppressElabErrors_1753_;
v___y_1741_ = v___y_1749_;
v___y_1742_ = v_ref_1757_;
v___y_1743_ = v___y_1750_;
v___y_1744_ = v_val_1760_;
goto v___jp_1737_;
}
}
v___jp_1762_:
{
if (v___y_1765_ == 0)
{
v___y_1748_ = v___y_1763_;
v___y_1749_ = v___y_1764_;
v___y_1750_ = v_severity_1668_;
goto v___jp_1747_;
}
else
{
v___y_1748_ = v___y_1763_;
v___y_1749_ = v___y_1764_;
v___y_1750_ = v___x_1761_;
goto v___jp_1747_;
}
}
v___jp_1766_:
{
if (v___y_1767_ == 0)
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = 1;
v___x_1769_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1668_, v___x_1768_);
if (v___x_1769_ == 0)
{
v___y_1763_ = v___y_1767_;
v___y_1764_ = v___y_1767_;
v___y_1765_ = v___x_1769_;
goto v___jp_1762_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1670_);
v___x_1771_ = l_Lean_warningAsError;
v___x_1772_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_1770_, v___x_1771_);
lean_dec_ref(v___x_1770_);
v___y_1763_ = v___y_1767_;
v___y_1764_ = v___y_1767_;
v___y_1765_ = v___x_1772_;
goto v___jp_1762_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec_ref(v_msgData_1667_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1777_, lean_object* v_msgData_1778_, lean_object* v_severity_1779_, lean_object* v_isSilent_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
uint8_t v_severity_boxed_1784_; uint8_t v_isSilent_boxed_1785_; lean_object* v_res_1786_; 
v_severity_boxed_1784_ = lean_unbox(v_severity_1779_);
v_isSilent_boxed_1785_ = lean_unbox(v_isSilent_1780_);
v_res_1786_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1777_, v_msgData_1778_, v_severity_boxed_1784_, v_isSilent_boxed_1785_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v_ref_1777_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1787_, uint8_t v_severity_1788_, uint8_t v_isSilent_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_ref_1793_; lean_object* v___x_1794_; 
v_ref_1793_ = lean_ctor_get(v___y_1790_, 2);
v___x_1794_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1793_, v_msgData_1787_, v_severity_1788_, v_isSilent_1789_, v___y_1790_, v___y_1791_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1795_, lean_object* v_severity_1796_, lean_object* v_isSilent_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v_severity_boxed_1801_; uint8_t v_isSilent_boxed_1802_; lean_object* v_res_1803_; 
v_severity_boxed_1801_ = lean_unbox(v_severity_1796_);
v_isSilent_boxed_1802_ = lean_unbox(v_isSilent_1797_);
v_res_1803_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1795_, v_severity_boxed_1801_, v_isSilent_boxed_1802_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = 1;
v___x_1809_ = 0;
v___x_1810_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1804_, v___x_1808_, v___x_1809_, v___y_1805_, v___y_1806_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msgData_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v_env_1821_; lean_object* v___x_1822_; lean_object* v_toEnvExtension_1823_; lean_object* v_asyncMode_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v_merged_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
v___x_1819_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1820_ = lean_st_ref_get(v___y_1817_);
v_env_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc_ref(v_env_1821_);
lean_dec(v___x_1820_);
v___x_1822_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1823_ = lean_ctor_get(v___x_1822_, 0);
v_asyncMode_1824_ = lean_ctor_get(v_toEnvExtension_1823_, 2);
v___x_1825_ = lean_box(0);
v___x_1826_ = 0;
v___x_1827_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1819_, v___x_1822_, v_env_1821_, v_asyncMode_1824_, v___x_1825_, v___x_1826_);
v_merged_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1827_, 1);
lean_dec(v_unused_1837_);
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_merged_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_merged_1828_);
lean_ctor_set(v___x_1830_, 0, v_o_1816_);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_o_1816_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_merged_1828_);
v___x_1833_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1838_, v___y_1839_);
lean_dec(v___y_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1842_);
v___x_1846_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v___x_1845_, v___y_1843_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_ref_1855_; lean_object* v___x_1856_; lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_ref_1855_ = lean_ctor_get(v___y_1852_, 2);
v___x_1856_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1851_, v___y_1852_, v___y_1853_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_inc(v_ref_1855_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_ref_1855_);
lean_ctor_set(v___x_1861_, 1, v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 1);
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___lam__0(lean_object* v___x_1871_, lean_object* v_entry_1872_, lean_object* v_s_1873_){
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1885_, lean_object* v_i_1886_, lean_object* v_k_1887_){
_start:
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_array_get_size(v_keys_1885_);
v___x_1889_ = lean_nat_dec_lt(v_i_1886_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_dec(v_i_1886_);
return v___x_1889_;
}
else
{
lean_object* v_k_x27_1890_; uint8_t v___x_1891_; 
v_k_x27_1890_ = lean_array_fget_borrowed(v_keys_1885_, v_i_1886_);
v___x_1891_ = l_Lean_instBEqExtraModUse_beq(v_k_1887_, v_k_x27_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = lean_nat_add(v_i_1886_, v___x_1892_);
lean_dec(v_i_1886_);
v_i_1886_ = v___x_1893_;
goto _start;
}
else
{
lean_dec(v_i_1886_);
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_1895_, lean_object* v_i_1896_, lean_object* v_k_1897_){
_start:
{
uint8_t v_res_1898_; lean_object* v_r_1899_; 
v_res_1898_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1895_, v_i_1896_, v_k_1897_);
lean_dec_ref(v_k_1897_);
lean_dec_ref(v_keys_1895_);
v_r_1899_ = lean_box(v_res_1898_);
return v_r_1899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_1900_, size_t v_x_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
lean_object* v_es_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; lean_object* v_j_1907_; lean_object* v___x_1908_; 
v_es_1903_ = lean_ctor_get(v_x_1900_, 0);
v___x_1904_ = lean_box(2);
v___x_1905_ = ((size_t)31ULL);
v___x_1906_ = lean_usize_land(v_x_1901_, v___x_1905_);
v_j_1907_ = lean_usize_to_nat(v___x_1906_);
v___x_1908_ = lean_array_get_borrowed(v___x_1904_, v_es_1903_, v_j_1907_);
lean_dec(v_j_1907_);
switch(lean_obj_tag(v___x_1908_))
{
case 0:
{
lean_object* v_key_1909_; uint8_t v___x_1910_; 
v_key_1909_ = lean_ctor_get(v___x_1908_, 0);
v___x_1910_ = l_Lean_instBEqExtraModUse_beq(v_x_1902_, v_key_1909_);
return v___x_1910_;
}
case 1:
{
lean_object* v_node_1911_; size_t v___x_1912_; size_t v___x_1913_; 
v_node_1911_ = lean_ctor_get(v___x_1908_, 0);
v___x_1912_ = ((size_t)5ULL);
v___x_1913_ = lean_usize_shift_right(v_x_1901_, v___x_1912_);
v_x_1900_ = v_node_1911_;
v_x_1901_ = v___x_1913_;
goto _start;
}
default: 
{
uint8_t v___x_1915_; 
v___x_1915_ = 0;
return v___x_1915_;
}
}
}
else
{
lean_object* v_ks_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_ks_1916_ = lean_ctor_get(v_x_1900_, 0);
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_1916_, v___x_1917_, v_x_1902_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
size_t v_x_45901__boxed_1922_; uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_x_45901__boxed_1922_ = lean_unbox_usize(v_x_1920_);
lean_dec(v_x_1920_);
v_res_1923_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1919_, v_x_45901__boxed_1922_, v_x_1921_);
lean_dec_ref(v_x_1921_);
lean_dec_ref(v_x_1919_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
uint64_t v___x_1927_; size_t v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = l_Lean_instHashableExtraModUse_hash(v_x_1926_);
v___x_1928_ = lean_uint64_to_usize(v___x_1927_);
v___x_1929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1925_, v___x_1928_, v_x_1926_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
uint8_t v_res_1932_; lean_object* v_r_1933_; 
v_res_1932_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1930_, v_x_1931_);
lean_dec_ref(v_x_1931_);
lean_dec_ref(v_x_1930_);
v_r_1933_ = lean_box(v_res_1932_);
return v_r_1933_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1934_; double v___x_1935_; 
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_float_of_nat(v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1938_, lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_ref_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1990_; 
v_ref_1943_ = lean_ctor_get(v___y_1940_, 2);
v___x_1944_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1939_, v___y_1940_, v___y_1941_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1990_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1990_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v_traceState_1950_; lean_object* v_env_1951_; lean_object* v_nextMacroScope_1952_; lean_object* v_ngen_1953_; lean_object* v_auxDeclNGen_1954_; lean_object* v_cache_1955_; lean_object* v_recordedDeps_1956_; lean_object* v_messages_1957_; lean_object* v_infoState_1958_; lean_object* v_snapshotTasks_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1989_; 
v___x_1949_ = lean_st_ref_take(v___y_1941_);
v_traceState_1950_ = lean_ctor_get(v___x_1949_, 4);
v_env_1951_ = lean_ctor_get(v___x_1949_, 0);
v_nextMacroScope_1952_ = lean_ctor_get(v___x_1949_, 1);
v_ngen_1953_ = lean_ctor_get(v___x_1949_, 2);
v_auxDeclNGen_1954_ = lean_ctor_get(v___x_1949_, 3);
v_cache_1955_ = lean_ctor_get(v___x_1949_, 5);
v_recordedDeps_1956_ = lean_ctor_get(v___x_1949_, 6);
v_messages_1957_ = lean_ctor_get(v___x_1949_, 7);
v_infoState_1958_ = lean_ctor_get(v___x_1949_, 8);
v_snapshotTasks_1959_ = lean_ctor_get(v___x_1949_, 9);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1961_ = v___x_1949_;
v_isShared_1962_ = v_isSharedCheck_1989_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_snapshotTasks_1959_);
lean_inc(v_infoState_1958_);
lean_inc(v_messages_1957_);
lean_inc(v_recordedDeps_1956_);
lean_inc(v_cache_1955_);
lean_inc(v_traceState_1950_);
lean_inc(v_auxDeclNGen_1954_);
lean_inc(v_ngen_1953_);
lean_inc(v_nextMacroScope_1952_);
lean_inc(v_env_1951_);
lean_dec(v___x_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1989_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
uint64_t v_tid_1963_; lean_object* v_traces_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1988_; 
v_tid_1963_ = lean_ctor_get_uint64(v_traceState_1950_, sizeof(void*)*1);
v_traces_1964_ = lean_ctor_get(v_traceState_1950_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_traceState_1950_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1966_ = v_traceState_1950_;
v_isShared_1967_ = v_isSharedCheck_1988_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_traces_1964_);
lean_dec(v_traceState_1950_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1988_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; double v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1971_ = 0;
v___x_1972_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1973_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1973_, 0, v_cls_1938_);
lean_ctor_set(v___x_1973_, 1, v___x_1969_);
lean_ctor_set(v___x_1973_, 2, v___x_1972_);
lean_ctor_set_float(v___x_1973_, sizeof(void*)*3, v___x_1970_);
lean_ctor_set_float(v___x_1973_, sizeof(void*)*3 + 8, v___x_1970_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*3 + 16, v___x_1971_);
v___x_1974_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1975_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v_a_1945_);
lean_ctor_set(v___x_1975_, 2, v___x_1974_);
lean_inc(v_ref_1943_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_ref_1943_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_PersistentArray_push___redArg(v_traces_1964_, v___x_1976_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1977_);
v___x_1979_ = v___x_1966_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1977_);
lean_ctor_set_uint64(v_reuseFailAlloc_1987_, sizeof(void*)*1, v_tid_1963_);
v___x_1979_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 4, v___x_1979_);
v___x_1981_ = v___x_1961_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_env_1951_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_nextMacroScope_1952_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_ngen_1953_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_auxDeclNGen_1954_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_cache_1955_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_recordedDeps_1956_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_messages_1957_);
lean_ctor_set(v_reuseFailAlloc_1986_, 8, v_infoState_1958_);
lean_ctor_set(v_reuseFailAlloc_1986_, 9, v_snapshotTasks_1959_);
v___x_1981_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_st_ref_put(v___y_1941_, v___x_1981_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1968_);
v___x_1984_ = v___x_1947_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1968_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1991_, v_msg_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1996_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2001_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_cls_2015_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2016_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_2017_ = l_Lean_Name_append(v___x_2016_, v_cls_2015_);
return v___x_2017_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2028_, uint8_t v_isMeta_2029_, lean_object* v_hint_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_env_2052_; uint8_t v_isExporting_2053_; lean_object* v_entry_2054_; lean_object* v___x_2055_; lean_object* v_env_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2050_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2);
v___x_2051_ = lean_st_ref_get(v___y_2032_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2051_);
v_isExporting_2053_ = lean_ctor_get_uint8(v_env_2052_, sizeof(void*)*13);
lean_dec_ref(v_env_2052_);
lean_inc(v_mod_2028_);
v_entry_2054_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2054_, 0, v_mod_2028_);
lean_ctor_set_uint8(v_entry_2054_, sizeof(void*)*1, v_isExporting_2053_);
lean_ctor_set_uint8(v_entry_2054_, sizeof(void*)*1 + 1, v_isMeta_2029_);
v___x_2055_ = lean_st_ref_get(v___y_2032_);
v_env_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_ref(v_env_2056_);
lean_dec(v___x_2055_);
v___x_2057_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2058_ = lean_box(1);
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2050_, v___x_2057_, v_env_2056_, v___x_2058_, v___x_2059_);
v___x_2061_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2060_, v_entry_2054_);
lean_dec(v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v_toCold_2062_; lean_object* v_options_2063_; lean_object* v_inheritedTraceOptions_2064_; uint8_t v_hasTrace_2065_; lean_object* v___f_2066_; uint8_t v___x_2067_; lean_object* v___y_2069_; 
v_toCold_2062_ = lean_ctor_get(v___y_2031_, 0);
v_options_2063_ = lean_ctor_get(v_toCold_2062_, 2);
v_inheritedTraceOptions_2064_ = lean_ctor_get(v_toCold_2062_, 11);
v_hasTrace_2065_ = lean_ctor_get_uint8(v_options_2063_, sizeof(void*)*1);
v___f_2066_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_2066_, 0, v___x_2057_);
lean_closure_set(v___f_2066_, 1, v_entry_2054_);
v___x_2067_ = 1;
if (v_hasTrace_2065_ == 0)
{
lean_dec(v_hint_2030_);
lean_dec(v_mod_2028_);
v___y_2069_ = v___y_2032_;
goto v___jp_2068_;
}
else
{
lean_object* v_cls_2087_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_cls_2087_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4));
v___x_2107_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2064_, v_options_2063_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec(v_hint_2030_);
lean_dec(v_mod_2028_);
v___y_2069_ = v___y_2032_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2109_; lean_object* v___y_2111_; 
v___x_2109_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13);
if (v_isExporting_2053_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___y_2111_ = v___x_2118_;
goto v___jp_2110_;
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_2111_ = v___x_2119_;
goto v___jp_2110_;
}
v___jp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_inc_ref(v___y_2111_);
v___x_2112_ = l_Lean_stringToMessageData(v___y_2111_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2109_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
if (v_isMeta_2029_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___y_2094_ = v___x_2115_;
v___y_2095_ = v___x_2116_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___y_2094_ = v___x_2115_;
v___y_2095_ = v___x_2117_;
goto v___jp_2093_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___y_2089_);
lean_ctor_set(v___x_2091_, 1, v___y_2090_);
v___x_2092_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2087_, v___x_2091_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
v___y_2069_ = v___y_2032_;
goto v___jp_2068_;
}
else
{
lean_dec_ref(v___f_2066_);
return v___x_2092_;
}
}
v___jp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
lean_inc_ref(v___y_2095_);
v___x_2096_ = l_Lean_stringToMessageData(v___y_2095_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___y_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = l_Lean_MessageData_ofName(v_mod_2028_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_Name_isAnonymous(v_hint_2030_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8);
v___x_2104_ = l_Lean_MessageData_ofName(v_hint_2030_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___y_2089_ = v___x_2101_;
v___y_2090_ = v___x_2105_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2106_; 
lean_dec(v_hint_2030_);
v___x_2106_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___y_2089_ = v___x_2101_;
v___y_2090_ = v___x_2106_;
goto v___jp_2088_;
}
}
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v_toEnvExtension_2071_; lean_object* v_env_2072_; lean_object* v_nextMacroScope_2073_; lean_object* v_ngen_2074_; lean_object* v_auxDeclNGen_2075_; lean_object* v_traceState_2076_; lean_object* v_recordedDeps_2077_; lean_object* v_messages_2078_; lean_object* v_infoState_2079_; lean_object* v_snapshotTasks_2080_; lean_object* v_asyncMode_2081_; uint8_t v_logWrites_2082_; lean_object* v___x_2083_; 
v___x_2070_ = lean_st_ref_take(v___y_2069_);
v_toEnvExtension_2071_ = lean_ctor_get(v___x_2057_, 0);
v_env_2072_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_ref(v_env_2072_);
v_nextMacroScope_2073_ = lean_ctor_get(v___x_2070_, 1);
lean_inc(v_nextMacroScope_2073_);
v_ngen_2074_ = lean_ctor_get(v___x_2070_, 2);
lean_inc_ref(v_ngen_2074_);
v_auxDeclNGen_2075_ = lean_ctor_get(v___x_2070_, 3);
lean_inc_ref(v_auxDeclNGen_2075_);
v_traceState_2076_ = lean_ctor_get(v___x_2070_, 4);
lean_inc_ref(v_traceState_2076_);
v_recordedDeps_2077_ = lean_ctor_get(v___x_2070_, 6);
lean_inc_ref(v_recordedDeps_2077_);
v_messages_2078_ = lean_ctor_get(v___x_2070_, 7);
lean_inc_ref(v_messages_2078_);
v_infoState_2079_ = lean_ctor_get(v___x_2070_, 8);
lean_inc_ref(v_infoState_2079_);
v_snapshotTasks_2080_ = lean_ctor_get(v___x_2070_, 9);
lean_inc_ref(v_snapshotTasks_2080_);
lean_dec(v___x_2070_);
v_asyncMode_2081_ = lean_ctor_get(v_toEnvExtension_2071_, 2);
v_logWrites_2082_ = lean_ctor_get_uint8(v_toEnvExtension_2071_, sizeof(void*)*6);
v___x_2083_ = lean_box(0);
if (v_logWrites_2082_ == 0)
{
lean_object* v___x_2084_; 
lean_inc_ref(v_toEnvExtension_2071_);
v___x_2084_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2071_, v_env_2072_, v___f_2066_, v_asyncMode_2081_, v___x_2059_, v___x_2067_);
v___y_2035_ = v_traceState_2076_;
v___y_2036_ = v_nextMacroScope_2073_;
v___y_2037_ = v___x_2083_;
v___y_2038_ = v_infoState_2079_;
v___y_2039_ = v_messages_2078_;
v___y_2040_ = v_auxDeclNGen_2075_;
v___y_2041_ = v___y_2069_;
v___y_2042_ = v_recordedDeps_2077_;
v___y_2043_ = v_snapshotTasks_2080_;
v___y_2044_ = v_ngen_2074_;
v___y_2045_ = v___x_2084_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc_ref_n(v_toEnvExtension_2071_, 2);
v___x_2085_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2071_, v_env_2072_);
lean_dec_ref(v_env_2072_);
v___x_2086_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2071_, v___x_2085_, v___f_2066_, v_asyncMode_2081_, v___x_2059_, v___x_2067_);
v___y_2035_ = v_traceState_2076_;
v___y_2036_ = v_nextMacroScope_2073_;
v___y_2037_ = v___x_2083_;
v___y_2038_ = v_infoState_2079_;
v___y_2039_ = v_messages_2078_;
v___y_2040_ = v_auxDeclNGen_2075_;
v___y_2041_ = v___y_2069_;
v___y_2042_ = v_recordedDeps_2077_;
v___y_2043_ = v_snapshotTasks_2080_;
v___y_2044_ = v_ngen_2074_;
v___y_2045_ = v___x_2086_;
goto v___jp_2034_;
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref_known(v_entry_2054_, 1);
lean_dec(v_hint_2030_);
lean_dec(v_mod_2028_);
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
v___jp_2034_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1);
v___x_2047_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2047_, 0, v___y_2045_);
lean_ctor_set(v___x_2047_, 1, v___y_2036_);
lean_ctor_set(v___x_2047_, 2, v___y_2044_);
lean_ctor_set(v___x_2047_, 3, v___y_2040_);
lean_ctor_set(v___x_2047_, 4, v___y_2035_);
lean_ctor_set(v___x_2047_, 5, v___x_2046_);
lean_ctor_set(v___x_2047_, 6, v___y_2042_);
lean_ctor_set(v___x_2047_, 7, v___y_2039_);
lean_ctor_set(v___x_2047_, 8, v___y_2038_);
lean_ctor_set(v___x_2047_, 9, v___y_2043_);
v___x_2048_ = lean_st_ref_put(v___y_2041_, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___y_2037_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2122_, lean_object* v_isMeta_2123_, lean_object* v_hint_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
uint8_t v_isMeta_boxed_2128_; lean_object* v_res_2129_; 
v_isMeta_boxed_2128_ = lean_unbox(v_isMeta_2123_);
v_res_2129_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_mod_2122_, v_isMeta_boxed_2128_, v_hint_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2130_, lean_object* v_declName_2131_, lean_object* v_as_2132_, size_t v_sz_2133_, size_t v_i_2134_, lean_object* v_b_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_2139_; 
v___x_2139_ = lean_usize_dec_lt(v_i_2134_, v_sz_2133_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec(v_declName_2131_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2135_);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v_modules_2142_; lean_object* v___x_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v_toImport_2146_; lean_object* v_module_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2141_ = l_Lean_Environment_header(v___x_2130_);
v_modules_2142_ = lean_ctor_get(v___x_2141_, 3);
lean_inc_ref(v_modules_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2144_ = lean_array_uget_borrowed(v_as_2132_, v_i_2134_);
v___x_2145_ = lean_array_get(v___x_2143_, v_modules_2142_, v_a_2144_);
lean_dec_ref(v_modules_2142_);
v_toImport_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_ref(v_toImport_2146_);
lean_dec(v___x_2145_);
v_module_2147_ = lean_ctor_get(v_toImport_2146_, 0);
lean_inc(v_module_2147_);
lean_dec_ref(v_toImport_2146_);
v___x_2148_ = lean_box(0);
v___x_2149_ = 0;
lean_inc(v_declName_2131_);
v___x_2150_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2147_, v___x_2149_, v_declName_2131_, v___y_2136_, v___y_2137_);
if (lean_obj_tag(v___x_2150_) == 0)
{
size_t v___x_2151_; size_t v___x_2152_; 
lean_dec_ref_known(v___x_2150_, 1);
v___x_2151_ = ((size_t)1ULL);
v___x_2152_ = lean_usize_add(v_i_2134_, v___x_2151_);
v_i_2134_ = v___x_2152_;
v_b_2135_ = v___x_2148_;
goto _start;
}
else
{
lean_dec(v_declName_2131_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2154_, lean_object* v_declName_2155_, lean_object* v_as_2156_, lean_object* v_sz_2157_, lean_object* v_i_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
size_t v_sz_boxed_2163_; size_t v_i_boxed_2164_; lean_object* v_res_2165_; 
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2157_);
lean_dec(v_sz_2157_);
v_i_boxed_2164_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v___x_2154_, v_declName_2155_, v_as_2156_, v_sz_boxed_2163_, v_i_boxed_2164_, v_b_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v_as_2156_);
lean_dec_ref(v___x_2154_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2166_, lean_object* v_x_2167_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
else
{
lean_object* v_key_2169_; lean_object* v_value_2170_; lean_object* v_tail_2171_; uint8_t v___x_2172_; 
v_key_2169_ = lean_ctor_get(v_x_2167_, 0);
v_value_2170_ = lean_ctor_get(v_x_2167_, 1);
v_tail_2171_ = lean_ctor_get(v_x_2167_, 2);
v___x_2172_ = lean_name_eq(v_key_2169_, v_a_2166_);
if (v___x_2172_ == 0)
{
v_x_2167_ = v_tail_2171_;
goto _start;
}
else
{
lean_object* v___x_2174_; 
lean_inc(v_value_2170_);
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_value_2170_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2175_, v_x_2176_);
lean_dec(v_x_2176_);
lean_dec(v_a_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_buckets_2180_; lean_object* v___x_2181_; uint64_t v___y_2183_; 
v_buckets_2180_ = lean_ctor_get(v_m_2178_, 1);
v___x_2181_ = lean_array_get_size(v_buckets_2180_);
if (lean_obj_tag(v_a_2179_) == 0)
{
uint64_t v___x_2197_; 
v___x_2197_ = 1723ULL;
v___y_2183_ = v___x_2197_;
goto v___jp_2182_;
}
else
{
uint64_t v_hash_2198_; 
v_hash_2198_ = lean_ctor_get_uint64(v_a_2179_, sizeof(void*)*2);
v___y_2183_ = v_hash_2198_;
goto v___jp_2182_;
}
v___jp_2182_:
{
uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v_fold_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2184_ = 32ULL;
v___x_2185_ = lean_uint64_shift_right(v___y_2183_, v___x_2184_);
v_fold_2186_ = lean_uint64_xor(v___y_2183_, v___x_2185_);
v___x_2187_ = 16ULL;
v___x_2188_ = lean_uint64_shift_right(v_fold_2186_, v___x_2187_);
v___x_2189_ = lean_uint64_xor(v_fold_2186_, v___x_2188_);
v___x_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = lean_usize_of_nat(v___x_2181_);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_sub(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_usize_land(v___x_2190_, v___x_2193_);
v___x_2195_ = lean_array_uget_borrowed(v_buckets_2180_, v___x_2194_);
v___x_2196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2179_, v___x_2195_);
return v___x_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_m_2199_);
return v_res_2201_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0(void){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(lean_object* v_declName_2205_, uint8_t v_isMeta_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_env_2215_; lean_object* v___y_2217_; lean_object* v___x_2230_; 
v___x_2210_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0);
v___x_2211_ = lean_st_ref_get(v___y_2208_);
v_env_2215_ = lean_ctor_get(v___x_2211_, 0);
lean_inc_ref(v_env_2215_);
lean_dec(v___x_2211_);
v___x_2230_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2215_, v_declName_2205_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_dec_ref(v_env_2215_);
lean_dec(v_declName_2205_);
goto v___jp_2212_;
}
else
{
lean_object* v_val_2231_; lean_object* v___x_2232_; lean_object* v_modules_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_val_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l_Lean_Environment_header(v_env_2215_);
v_modules_2233_ = lean_ctor_get(v___x_2232_, 3);
lean_inc_ref(v_modules_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = lean_array_get_size(v_modules_2233_);
v___x_2235_ = lean_nat_dec_lt(v_val_2231_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v_modules_2233_);
lean_dec(v_val_2231_);
lean_dec_ref(v_env_2215_);
lean_dec(v_declName_2205_);
goto v___jp_2212_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___y_2239_; 
v___x_2236_ = lean_array_fget(v_modules_2233_, v_val_2231_);
lean_dec(v_val_2231_);
lean_dec_ref(v_modules_2233_);
v___x_2237_ = lean_st_ref_get(v___y_2208_);
if (v_isMeta_2206_ == 0)
{
lean_dec(v___x_2237_);
v___y_2239_ = v_isMeta_2206_;
goto v___jp_2238_;
}
else
{
lean_object* v_env_2250_; uint8_t v___x_2251_; 
v_env_2250_ = lean_ctor_get(v___x_2237_, 0);
lean_inc_ref(v_env_2250_);
lean_dec(v___x_2237_);
lean_inc(v_declName_2205_);
v___x_2251_ = l_Lean_isMarkedMeta(v_env_2250_, v_declName_2205_);
if (v___x_2251_ == 0)
{
v___y_2239_ = v_isMeta_2206_;
goto v___jp_2238_;
}
else
{
uint8_t v___x_2252_; 
v___x_2252_ = 0;
v___y_2239_ = v___x_2252_;
goto v___jp_2238_;
}
}
v___jp_2238_:
{
lean_object* v_toImport_2240_; lean_object* v_module_2241_; lean_object* v___x_2242_; 
v_toImport_2240_ = lean_ctor_get(v___x_2236_, 0);
lean_inc_ref(v_toImport_2240_);
lean_dec(v___x_2236_);
v_module_2241_ = lean_ctor_get(v_toImport_2240_, 0);
lean_inc(v_module_2241_);
lean_dec_ref(v_toImport_2240_);
lean_inc(v_declName_2205_);
v___x_2242_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2241_, v___y_2239_, v_declName_2205_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2243_ = l_Lean_indirectModUseExt;
v___x_2244_ = lean_box(1);
v___x_2245_ = lean_box(0);
lean_inc_ref(v_env_2215_);
v___x_2246_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2210_, v___x_2243_, v_env_2215_, v___x_2244_, v___x_2245_);
v___x_2247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2246_, v_declName_2205_);
lean_dec(v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1));
v___y_2217_ = v___x_2248_;
goto v___jp_2216_;
}
else
{
lean_object* v_val_2249_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2247_, 1);
v___y_2217_ = v_val_2249_;
goto v___jp_2216_;
}
}
else
{
lean_dec_ref(v_env_2215_);
lean_dec(v_declName_2205_);
return v___x_2242_;
}
}
}
}
v___jp_2212_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
v___jp_2216_:
{
lean_object* v___x_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v___x_2218_ = lean_box(0);
v_sz_2219_ = lean_array_size(v___y_2217_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v_env_2215_, v_declName_2205_, v___y_2217_, v_sz_2219_, v___x_2220_, v___x_2218_, v___y_2207_, v___y_2208_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_env_2215_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2221_, 0);
lean_dec(v_unused_2229_);
v___x_2223_ = v___x_2221_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v___x_2221_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2218_);
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2218_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2253_, lean_object* v_isMeta_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v_isMeta_boxed_2258_; lean_object* v_res_2259_; 
v_isMeta_boxed_2258_ = lean_unbox(v_isMeta_2254_);
v_res_2259_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_declName_2253_, v_isMeta_boxed_2258_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2259_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2264_ = l_Lean_MessageData_ofFormat(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2269_ = l_Lean_MessageData_ofFormat(v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2278_ = l_Lean_stringToMessageData(v___x_2277_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2283_ = l_Lean_MessageData_ofFormat(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2285_ = l_Lean_MessageData_hint_x27(v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2293_ = l_Lean_MessageData_ofFormat(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2301_ = l_Lean_MessageData_ofFormat(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2311_ = lean_box(1);
v___x_2312_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2313_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2312_);
lean_ctor_set(v___x_2314_, 2, v___x_2311_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2318_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
lean_ctor_set(v___x_2320_, 3, v___x_2319_);
lean_ctor_set(v___x_2320_, 4, v___x_2318_);
lean_ctor_set(v___x_2320_, 5, v___x_2318_);
lean_ctor_set(v___x_2320_, 6, v___x_2318_);
lean_ctor_set(v___x_2320_, 7, v___x_2318_);
lean_ctor_set(v___x_2320_, 8, v___x_2318_);
lean_ctor_set(v___x_2320_, 9, v___x_2318_);
lean_ctor_set(v___x_2320_, 10, v___x_2318_);
lean_ctor_set(v___x_2320_, 11, v___x_2317_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
lean_ctor_set(v___x_2322_, 2, v___x_2321_);
lean_ctor_set(v___x_2322_, 3, v___x_2321_);
lean_ctor_set(v___x_2322_, 4, v___x_2321_);
lean_ctor_set(v___x_2322_, 5, v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
lean_ctor_set(v___x_2324_, 2, v___x_2323_);
lean_ctor_set(v___x_2324_, 3, v___x_2323_);
lean_ctor_set(v___x_2324_, 4, v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2342_ = l_Lean_stringToMessageData(v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2357_ = l_Lean_stringToMessageData(v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2360_ = l_Lean_stringToMessageData(v___x_2359_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v___f_2366_, uint8_t v___x_2367_, lean_object* v___x_2368_, lean_object* v___x_2369_, lean_object* v_a_2370_, lean_object* v_declName_2371_, lean_object* v_stx_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v_hint_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; 
v___x_2382_ = l_Lean_Name_mkStr2(v___x_2364_, v___x_2365_);
lean_inc(v_stx_2372_);
v___x_2383_ = l_Lean_Syntax_isOfKind(v_stx_2372_, v___x_2382_);
lean_dec(v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v_stx_2372_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2492_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2493_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2492_, v___y_2373_, v___y_2374_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v_val_2505_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; uint8_t v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; uint8_t v_a_2552_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; uint8_t v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v_msg_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v_a_2646_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_a_2790_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v_since_x3f_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v_typeChanged_x3f_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2846_; lean_object* v_text_x3f_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v_id_x3f_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2872_ = l_Lean_Syntax_getArg(v_stx_2372_, v___x_2495_);
v___x_2873_ = l_Lean_Syntax_isNone(v___x_2872_);
if (v___x_2873_ == 0)
{
uint8_t v___x_2874_; 
lean_inc(v___x_2872_);
v___x_2874_ = l_Lean_Syntax_matchesNull(v___x_2872_, v___x_2495_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec(v___x_2872_);
lean_dec(v_stx_2372_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2875_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2876_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2875_, v___y_2373_, v___y_2374_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = l_Lean_Syntax_getArg(v___x_2872_, v___x_2494_);
lean_dec(v___x_2872_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
v_id_x3f_2860_ = v___x_2878_;
v___y_2861_ = v___y_2373_;
v___y_2862_ = v___y_2374_;
goto v___jp_2859_;
}
}
else
{
lean_object* v___x_2879_; 
lean_dec(v___x_2872_);
v___x_2879_ = lean_box(0);
v_id_x3f_2860_ = v___x_2879_;
v___y_2861_ = v___y_2373_;
v___y_2862_ = v___y_2374_;
goto v___jp_2859_;
}
v___jp_2496_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2506_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2507_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___f_2366_);
v___x_2511_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2507_);
lean_ctor_set(v___x_2511_, 1, v___x_2508_);
lean_ctor_set(v___x_2511_, 2, v___x_2508_);
lean_ctor_set(v___x_2511_, 3, v___x_2508_);
lean_ctor_set(v___x_2511_, 4, v___x_2509_);
lean_ctor_set(v___x_2511_, 5, v___x_2510_);
lean_inc(v_val_2505_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_val_2505_);
lean_ctor_set(v___x_2512_, 1, v_val_2505_);
v___x_2513_ = l_Lean_Syntax_ofRange(v___x_2512_, v___x_2383_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
v___x_2515_ = 4;
v___x_2516_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2516_, 0, v___x_2511_);
lean_ctor_set(v___x_2516_, 1, v___x_2514_);
lean_ctor_set(v___x_2516_, 2, v___x_2508_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*3, v___x_2515_);
v___x_2517_ = lean_mk_empty_array_with_capacity(v___x_2495_);
v___x_2518_ = lean_array_push(v___x_2517_, v___x_2516_);
v___x_2519_ = l_Lean_MessageData_hint(v___x_2506_, v___x_2518_, v___x_2508_, v___x_2508_, v___x_2367_, v___y_2504_, v___y_2497_);
lean_dec_ref(v___x_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___y_2452_ = v___y_2498_;
v___y_2453_ = v___y_2499_;
v___y_2454_ = v___y_2500_;
v___y_2455_ = v___y_2503_;
v___y_2456_ = v___y_2502_;
v___y_2457_ = v___y_2501_;
v_hint_2458_ = v_a_2520_;
v___y_2459_ = v___y_2504_;
v___y_2460_ = v___y_2497_;
goto v___jp_2451_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
v_a_2521_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2519_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
v___jp_2529_:
{
if (lean_obj_tag(v___y_2532_) == 0)
{
lean_dec_ref(v___f_2366_);
v___y_2483_ = v___y_2530_;
v___y_2484_ = v___y_2531_;
v___y_2485_ = v___y_2532_;
v___y_2486_ = v___y_2533_;
v___y_2487_ = v___y_2537_;
v___y_2488_ = v___y_2536_;
v___y_2489_ = v___y_2535_;
v___y_2490_ = v___y_2534_;
goto v___jp_2482_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2539_; 
v_val_2538_ = lean_ctor_get(v___y_2532_, 0);
v___x_2539_ = l_Lean_Syntax_getTailPos_x3f(v_val_2538_, v___x_2383_);
if (lean_obj_tag(v___x_2539_) == 1)
{
lean_object* v_val_2540_; 
v_val_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2531_;
v___y_2499_ = v___y_2532_;
v___y_2500_ = v___y_2533_;
v___y_2501_ = v___y_2537_;
v___y_2502_ = v___y_2536_;
v___y_2503_ = v___y_2535_;
v___y_2504_ = v___y_2534_;
v_val_2505_ = v_val_2540_;
goto v___jp_2496_;
}
else
{
lean_dec(v___x_2539_);
lean_dec_ref(v___f_2366_);
v___y_2483_ = v___y_2530_;
v___y_2484_ = v___y_2531_;
v___y_2485_ = v___y_2532_;
v___y_2486_ = v___y_2533_;
v___y_2487_ = v___y_2537_;
v___y_2488_ = v___y_2536_;
v___y_2489_ = v___y_2535_;
v___y_2490_ = v___y_2534_;
goto v___jp_2482_;
}
}
}
v___jp_2541_:
{
if (v_a_2552_ == 0)
{
if (lean_obj_tag(v___y_2543_) == 0)
{
if (v___y_2542_ == 0)
{
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2546_;
v___y_2436_ = v___y_2551_;
v___y_2437_ = v___y_2550_;
v___y_2438_ = v___y_2549_;
v___y_2439_ = v___y_2548_;
v___y_2440_ = v___y_2544_;
goto v___jp_2434_;
}
else
{
if (lean_obj_tag(v___y_2551_) == 0)
{
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2545_;
v___y_2532_ = v___y_2546_;
v___y_2533_ = v___y_2547_;
v___y_2534_ = v___y_2548_;
v___y_2535_ = v___y_2549_;
v___y_2536_ = v___y_2550_;
v___y_2537_ = v___y_2551_;
goto v___jp_2529_;
}
else
{
lean_object* v_val_2553_; lean_object* v___x_2554_; 
v_val_2553_ = lean_ctor_get(v___y_2551_, 0);
v___x_2554_ = l_Lean_Syntax_getTailPos_x3f(v_val_2553_, v___x_2383_);
if (lean_obj_tag(v___x_2554_) == 0)
{
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2545_;
v___y_2532_ = v___y_2546_;
v___y_2533_ = v___y_2547_;
v___y_2534_ = v___y_2548_;
v___y_2535_ = v___y_2549_;
v___y_2536_ = v___y_2550_;
v___y_2537_ = v___y_2551_;
goto v___jp_2529_;
}
else
{
lean_object* v_val_2555_; 
v_val_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___y_2497_ = v___y_2544_;
v___y_2498_ = v___y_2545_;
v___y_2499_ = v___y_2546_;
v___y_2500_ = v___y_2547_;
v___y_2501_ = v___y_2551_;
v___y_2502_ = v___y_2550_;
v___y_2503_ = v___y_2549_;
v___y_2504_ = v___y_2548_;
v_val_2505_ = v_val_2555_;
goto v___jp_2496_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2543_, 1);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2546_;
v___y_2436_ = v___y_2551_;
v___y_2437_ = v___y_2550_;
v___y_2438_ = v___y_2549_;
v___y_2439_ = v___y_2548_;
v___y_2440_ = v___y_2544_;
goto v___jp_2434_;
}
}
else
{
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2366_);
if (lean_obj_tag(v___y_2543_) == 0)
{
v___y_2435_ = v___y_2546_;
v___y_2436_ = v___y_2551_;
v___y_2437_ = v___y_2550_;
v___y_2438_ = v___y_2549_;
v___y_2439_ = v___y_2548_;
v___y_2440_ = v___y_2544_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec_ref_known(v___y_2543_, 1);
v___x_2556_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2557_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2556_, v___y_2548_, v___y_2544_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_dec_ref_known(v___x_2557_, 1);
v___y_2435_ = v___y_2546_;
v___y_2436_ = v___y_2551_;
v___y_2437_ = v___y_2550_;
v___y_2438_ = v___y_2549_;
v___y_2439_ = v___y_2548_;
v___y_2440_ = v___y_2544_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec(v___y_2546_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
v___jp_2566_:
{
lean_object* v___x_2577_; 
lean_inc_ref(v___y_2570_);
v___x_2577_ = l_Lean_Environment_find_x3f(v___y_2570_, v_declName_2371_, v___x_2367_);
if (lean_obj_tag(v___x_2577_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2579_; 
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = l_Lean_Environment_find_x3f(v___y_2570_, v___y_2574_, v___x_2367_);
if (lean_obj_tag(v___x_2579_) == 1)
{
lean_object* v_val_2580_; uint8_t v___x_2581_; uint8_t v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; uint64_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_val_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = 1;
v___x_2582_ = 0;
v___x_2583_ = 2;
v___x_2584_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2584_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 1, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 2, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 3, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 4, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 5, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 6, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 7, v___x_2367_);
lean_ctor_set_uint8(v___x_2584_, 8, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 9, v___x_2581_);
lean_ctor_set_uint8(v___x_2584_, 10, v___x_2582_);
lean_ctor_set_uint8(v___x_2584_, 11, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 12, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 13, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 14, v___x_2583_);
lean_ctor_set_uint8(v___x_2584_, 15, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 16, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 17, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 18, v___y_2567_);
lean_ctor_set_uint8(v___x_2584_, 19, v___x_2367_);
v___x_2585_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set_uint64(v___x_2586_, sizeof(void*)*1, v___x_2585_);
v___x_2587_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2588_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2589_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2590_ = lean_box(0);
lean_inc(v___x_2368_);
v___x_2591_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2591_, 0, v___x_2586_);
lean_ctor_set(v___x_2591_, 1, v___x_2368_);
lean_ctor_set(v___x_2591_, 2, v___x_2588_);
lean_ctor_set(v___x_2591_, 3, v___x_2589_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
lean_ctor_set(v___x_2591_, 5, v___x_2494_);
lean_ctor_set(v___x_2591_, 6, v___x_2590_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7, v___x_2367_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 1, v___x_2367_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 2, v___x_2367_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 3, v___x_2383_);
v___x_2592_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2593_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2594_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2592_);
lean_ctor_set(v___x_2595_, 1, v___x_2593_);
lean_ctor_set(v___x_2595_, 2, v___x_2368_);
lean_ctor_set(v___x_2595_, 3, v___x_2587_);
lean_ctor_set(v___x_2595_, 4, v___x_2594_);
v___x_2596_ = lean_st_mk_ref(v___x_2595_);
v___x_2597_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2578_, v_val_2580_, v___x_2591_, v___x_2596_, v___y_2575_, v___y_2576_);
lean_dec_ref_known(v___x_2591_, 7);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_st_ref_get(v___x_2596_);
lean_dec(v___x_2596_);
lean_dec(v___x_2599_);
v___x_2600_ = lean_unbox(v_a_2598_);
lean_dec(v_a_2598_);
v___y_2542_ = v___y_2567_;
v___y_2543_ = v___y_2568_;
v___y_2544_ = v___y_2576_;
v___y_2545_ = v_val_2580_;
v___y_2546_ = v___y_2569_;
v___y_2547_ = v_val_2578_;
v___y_2548_ = v___y_2575_;
v___y_2549_ = v___y_2573_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2571_;
v_a_2552_ = v___x_2600_;
goto v___jp_2541_;
}
else
{
lean_dec(v___x_2596_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2601_; uint8_t v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2602_ = lean_unbox(v_a_2601_);
lean_dec(v_a_2601_);
v___y_2542_ = v___y_2567_;
v___y_2543_ = v___y_2568_;
v___y_2544_ = v___y_2576_;
v___y_2545_ = v_val_2580_;
v___y_2546_ = v___y_2569_;
v___y_2547_ = v_val_2578_;
v___y_2548_ = v___y_2575_;
v___y_2549_ = v___y_2573_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2571_;
v_a_2552_ = v___x_2602_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_val_2580_);
lean_dec(v_val_2578_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___f_2366_);
v_a_2603_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2597_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2597_);
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
}
else
{
lean_dec(v___x_2579_);
lean_dec(v_val_2578_);
lean_dec(v___y_2568_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2569_;
v___y_2436_ = v___y_2571_;
v___y_2437_ = v___y_2572_;
v___y_2438_ = v___y_2573_;
v___y_2439_ = v___y_2575_;
v___y_2440_ = v___y_2576_;
goto v___jp_2434_;
}
}
else
{
lean_dec(v___x_2577_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2568_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2569_;
v___y_2436_ = v___y_2571_;
v___y_2437_ = v___y_2572_;
v___y_2438_ = v___y_2573_;
v___y_2439_ = v___y_2575_;
v___y_2440_ = v___y_2576_;
goto v___jp_2434_;
}
}
v___jp_2611_:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msg_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_dec_ref_known(v___x_2623_, 1);
v___y_2567_ = v___y_2612_;
v___y_2568_ = v___y_2613_;
v___y_2569_ = v___y_2615_;
v___y_2570_ = v___y_2614_;
v___y_2571_ = v___y_2619_;
v___y_2572_ = v___y_2618_;
v___y_2573_ = v___y_2617_;
v___y_2574_ = v___y_2616_;
v___y_2575_ = v___y_2621_;
v___y_2576_ = v___y_2622_;
goto v___jp_2566_;
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v_declName_2371_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
v___jp_2632_:
{
if (lean_obj_tag(v_a_2646_) == 1)
{
lean_object* v_val_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2677_; 
v_val_2647_ = lean_ctor_get(v_a_2646_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2649_ = v_a_2646_;
v_isShared_2650_ = v_isSharedCheck_2677_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_val_2647_);
lean_dec(v_a_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2677_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2651_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v___y_2636_);
v___x_2653_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = l_Lean_Name_toString(v_val_2647_, v___x_2383_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
lean_ctor_set(v___x_2658_, 2, v___x_2657_);
lean_ctor_set(v___x_2658_, 3, v___x_2657_);
lean_ctor_set(v___x_2658_, 4, v___x_2657_);
lean_ctor_set(v___x_2658_, 5, v___x_2657_);
v___x_2659_ = 0;
v___x_2660_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2657_);
lean_ctor_set(v___x_2660_, 2, v___x_2657_);
lean_ctor_set_uint8(v___x_2660_, sizeof(void*)*3, v___x_2659_);
v___x_2661_ = lean_mk_empty_array_with_capacity(v___x_2495_);
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2660_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___y_2635_);
v___x_2664_ = v___x_2649_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___y_2635_);
v___x_2664_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_MessageData_hint(v___x_2654_, v___x_2662_, v___x_2664_, v___x_2657_, v___x_2367_, v___y_2641_, v___y_2644_);
lean_dec_ref(v___x_2662_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2633_);
lean_ctor_set(v___x_2667_, 1, v_a_2666_);
v___y_2612_ = v___y_2640_;
v___y_2613_ = v___y_2634_;
v___y_2614_ = v___y_2642_;
v___y_2615_ = v___y_2643_;
v___y_2616_ = v___y_2637_;
v___y_2617_ = v___y_2645_;
v___y_2618_ = v___y_2638_;
v___y_2619_ = v___y_2639_;
v_msg_2620_ = v___x_2667_;
v___y_2621_ = v___y_2641_;
v___y_2622_ = v___y_2644_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v___y_2645_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v_declName_2371_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2668_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2665_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2665_);
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
}
}
else
{
lean_dec(v_a_2646_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
v___y_2612_ = v___y_2640_;
v___y_2613_ = v___y_2634_;
v___y_2614_ = v___y_2642_;
v___y_2615_ = v___y_2643_;
v___y_2616_ = v___y_2637_;
v___y_2617_ = v___y_2645_;
v___y_2618_ = v___y_2638_;
v___y_2619_ = v___y_2639_;
v_msg_2620_ = v___y_2633_;
v___y_2621_ = v___y_2641_;
v___y_2622_ = v___y_2644_;
goto v___jp_2611_;
}
}
v___jp_2678_:
{
if (lean_obj_tag(v___y_2683_) == 1)
{
lean_object* v_val_2686_; lean_object* v___x_2687_; 
v_val_2686_ = lean_ctor_get(v___y_2683_, 0);
lean_inc(v_val_2686_);
v___x_2687_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_val_2686_, v___x_2367_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; lean_object* v_a_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
lean_dec_ref_known(v___x_2687_, 1);
v___x_2688_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_2684_, v___y_2685_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = l_Lean_Linter_linter_deprecated;
v___x_2691_ = l_Lean_Linter_getLinterValue(v___x_2690_, v_a_2689_);
lean_dec(v_a_2689_);
if (v___x_2691_ == 0)
{
lean_dec(v___y_2679_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2680_;
v___y_2436_ = v___y_2682_;
v___y_2437_ = v___y_2683_;
v___y_2438_ = v___y_2681_;
v___y_2439_ = v___y_2684_;
v___y_2440_ = v___y_2685_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2692_; lean_object* v_env_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
lean_inc(v_val_2686_);
v___x_2692_ = lean_st_ref_get(v___y_2685_);
v_env_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_ref(v_env_2693_);
lean_dec(v___x_2692_);
v___x_2694_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2684_);
v___x_2695_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2696_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v___x_2694_, v___x_2695_);
lean_dec_ref(v___x_2694_);
if (v___x_2696_ == 0)
{
lean_dec_ref(v___x_2369_);
v___y_2567_ = v___x_2691_;
v___y_2568_ = v___y_2679_;
v___y_2569_ = v___y_2680_;
v___y_2570_ = v_env_2693_;
v___y_2571_ = v___y_2682_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2681_;
v___y_2574_ = v_val_2686_;
v___y_2575_ = v___y_2684_;
v___y_2576_ = v___y_2685_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2697_; 
lean_inc(v_val_2686_);
lean_inc_ref(v_env_2693_);
v___x_2697_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2369_, v_a_2370_, v___x_2367_, v_env_2693_, v_val_2686_);
if (lean_obj_tag(v___x_2697_) == 1)
{
lean_object* v_val_2698_; lean_object* v_name_2699_; lean_object* v_newName_x3f_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_val_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v_name_2699_ = lean_ctor_get(v___x_2695_, 0);
v_newName_x3f_2700_ = lean_ctor_get(v_val_2698_, 0);
lean_inc(v_newName_x3f_2700_);
lean_dec(v_val_2698_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_name_2699_);
v___x_2702_ = l_Lean_MessageData_ofName(v_name_2699_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_MessageData_note(v___x_2705_);
if (lean_obj_tag(v_newName_x3f_2700_) == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2686_);
v___x_2708_ = l_Lean_MessageData_ofConstName(v_val_2686_, v___x_2383_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
lean_inc(v_declName_2371_);
v___x_2712_ = l_Lean_MessageData_ofConstName(v_declName_2371_, v___x_2383_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___x_2706_);
v___x_2717_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2716_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_dec_ref_known(v___x_2717_, 1);
v___y_2567_ = v___x_2691_;
v___y_2568_ = v___y_2679_;
v___y_2569_ = v___y_2680_;
v___y_2570_ = v_env_2693_;
v___y_2571_ = v___y_2682_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2681_;
v___y_2574_ = v_val_2686_;
v___y_2575_ = v___y_2684_;
v___y_2576_ = v___y_2685_;
goto v___jp_2566_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec_ref(v_env_2693_);
lean_dec(v_val_2686_);
lean_dec_ref_known(v___y_2683_, 1);
lean_dec(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v_declName_2371_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v_val_2726_; uint8_t v___x_2727_; 
v_val_2726_ = lean_ctor_get(v_newName_x3f_2700_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_newName_x3f_2700_, 1);
v___x_2727_ = lean_name_eq(v_val_2726_, v_val_2686_);
if (v___x_2727_ == 0)
{
if (v___x_2696_ == 0)
{
lean_dec(v_val_2726_);
lean_dec_ref(v___x_2706_);
v___y_2567_ = v___x_2691_;
v___y_2568_ = v___y_2679_;
v___y_2569_ = v___y_2680_;
v___y_2570_ = v_env_2693_;
v___y_2571_ = v___y_2682_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2681_;
v___y_2574_ = v_val_2686_;
v___y_2575_ = v___y_2684_;
v___y_2576_ = v___y_2685_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2728_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2686_);
v___x_2729_ = l_Lean_MessageData_ofConstName(v_val_2686_, v___x_2383_);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
lean_inc(v_val_2726_);
v___x_2733_ = l_Lean_MessageData_ofConstName(v_val_2726_, v___x_2383_);
lean_inc_ref_n(v___x_2733_, 2);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
lean_inc(v_declName_2371_);
v___x_2737_ = l_Lean_MessageData_ofConstName(v_declName_2371_, v___x_2383_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v___x_2733_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___x_2706_);
if (lean_obj_tag(v___y_2680_) == 1)
{
lean_object* v_val_2745_; lean_object* v___x_2746_; 
v_val_2745_ = lean_ctor_get(v___y_2680_, 0);
v___x_2746_ = l_Lean_Syntax_getRange_x3f(v_val_2745_, v___x_2383_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_dec_ref(v___x_2733_);
lean_dec(v_val_2726_);
v___y_2612_ = v___x_2691_;
v___y_2613_ = v___y_2679_;
v___y_2614_ = v_env_2693_;
v___y_2615_ = v___y_2680_;
v___y_2616_ = v_val_2686_;
v___y_2617_ = v___y_2681_;
v___y_2618_ = v___y_2683_;
v___y_2619_ = v___y_2682_;
v_msg_2620_ = v___x_2744_;
v___y_2621_ = v___y_2684_;
v___y_2622_ = v___y_2685_;
goto v___jp_2611_;
}
else
{
uint8_t v___x_2747_; uint8_t v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; uint64_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_inc(v_val_2745_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2747_ = 1;
v___x_2748_ = 0;
v___x_2749_ = 2;
v___x_2750_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2750_, 0, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 1, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 2, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 3, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 4, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 5, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 6, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 7, v___x_2727_);
lean_ctor_set_uint8(v___x_2750_, 8, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 9, v___x_2747_);
lean_ctor_set_uint8(v___x_2750_, 10, v___x_2748_);
lean_ctor_set_uint8(v___x_2750_, 11, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 12, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 13, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 14, v___x_2749_);
lean_ctor_set_uint8(v___x_2750_, 15, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 16, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 17, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 18, v___x_2696_);
lean_ctor_set_uint8(v___x_2750_, 19, v___x_2727_);
v___x_2751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set_uint64(v___x_2752_, sizeof(void*)*1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2754_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2756_ = lean_box(0);
lean_inc_n(v___x_2368_, 2);
v___x_2757_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2757_, 0, v___x_2752_);
lean_ctor_set(v___x_2757_, 1, v___x_2368_);
lean_ctor_set(v___x_2757_, 2, v___x_2754_);
lean_ctor_set(v___x_2757_, 3, v___x_2755_);
lean_ctor_set(v___x_2757_, 4, v___x_2756_);
lean_ctor_set(v___x_2757_, 5, v___x_2494_);
lean_ctor_set(v___x_2757_, 6, v___x_2756_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*7, v___x_2367_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*7 + 1, v___x_2367_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*7 + 2, v___x_2367_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*7 + 3, v___x_2383_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2759_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2760_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2758_);
lean_ctor_set(v___x_2761_, 1, v___x_2759_);
lean_ctor_set(v___x_2761_, 2, v___x_2368_);
lean_ctor_set(v___x_2761_, 3, v___x_2753_);
lean_ctor_set(v___x_2761_, 4, v___x_2760_);
v___x_2762_ = lean_st_mk_ref(v___x_2761_);
v___x_2763_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_val_2726_, v___x_2367_, v___x_2757_, v___x_2762_, v___y_2684_, v___y_2685_);
lean_dec_ref_known(v___x_2757_, 7);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = lean_st_ref_get(v___x_2762_);
lean_dec(v___x_2762_);
lean_dec(v___x_2765_);
v___y_2633_ = v___x_2744_;
v___y_2634_ = v___y_2679_;
v___y_2635_ = v_val_2745_;
v___y_2636_ = v___x_2733_;
v___y_2637_ = v_val_2686_;
v___y_2638_ = v___y_2683_;
v___y_2639_ = v___y_2682_;
v___y_2640_ = v___x_2691_;
v___y_2641_ = v___y_2684_;
v___y_2642_ = v_env_2693_;
v___y_2643_ = v___y_2680_;
v___y_2644_ = v___y_2685_;
v___y_2645_ = v___y_2681_;
v_a_2646_ = v_a_2764_;
goto v___jp_2632_;
}
else
{
lean_dec(v___x_2762_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2763_, 1);
v___y_2633_ = v___x_2744_;
v___y_2634_ = v___y_2679_;
v___y_2635_ = v_val_2745_;
v___y_2636_ = v___x_2733_;
v___y_2637_ = v_val_2686_;
v___y_2638_ = v___y_2683_;
v___y_2639_ = v___y_2682_;
v___y_2640_ = v___x_2691_;
v___y_2641_ = v___y_2684_;
v___y_2642_ = v_env_2693_;
v___y_2643_ = v___y_2680_;
v___y_2644_ = v___y_2685_;
v___y_2645_ = v___y_2681_;
v_a_2646_ = v_a_2766_;
goto v___jp_2632_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_val_2745_);
lean_dec_ref_known(v___y_2680_, 1);
lean_dec_ref_known(v___x_2744_, 2);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_env_2693_);
lean_dec_ref_known(v___y_2683_, 1);
lean_dec(v_val_2686_);
lean_dec(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2679_);
lean_dec(v_declName_2371_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2767_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2763_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2763_);
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
lean_dec_ref(v___x_2733_);
lean_dec(v_val_2726_);
v___y_2612_ = v___x_2691_;
v___y_2613_ = v___y_2679_;
v___y_2614_ = v_env_2693_;
v___y_2615_ = v___y_2680_;
v___y_2616_ = v_val_2686_;
v___y_2617_ = v___y_2681_;
v___y_2618_ = v___y_2683_;
v___y_2619_ = v___y_2682_;
v_msg_2620_ = v___x_2744_;
v___y_2621_ = v___y_2684_;
v___y_2622_ = v___y_2685_;
goto v___jp_2611_;
}
}
}
else
{
lean_dec(v_val_2726_);
lean_dec_ref(v___x_2706_);
v___y_2567_ = v___x_2691_;
v___y_2568_ = v___y_2679_;
v___y_2569_ = v___y_2680_;
v___y_2570_ = v_env_2693_;
v___y_2571_ = v___y_2682_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2681_;
v___y_2574_ = v_val_2686_;
v___y_2575_ = v___y_2684_;
v___y_2576_ = v___y_2685_;
goto v___jp_2566_;
}
}
}
else
{
lean_dec(v___x_2697_);
v___y_2567_ = v___x_2691_;
v___y_2568_ = v___y_2679_;
v___y_2569_ = v___y_2680_;
v___y_2570_ = v_env_2693_;
v___y_2571_ = v___y_2682_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2681_;
v___y_2574_ = v_val_2686_;
v___y_2575_ = v___y_2684_;
v___y_2576_ = v___y_2685_;
goto v___jp_2566_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref_known(v___y_2683_, 1);
lean_dec(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2775_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2687_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2687_);
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
lean_dec(v___y_2679_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___y_2435_ = v___y_2680_;
v___y_2436_ = v___y_2682_;
v___y_2437_ = v___y_2683_;
v___y_2438_ = v___y_2681_;
v___y_2439_ = v___y_2684_;
v___y_2440_ = v___y_2685_;
goto v___jp_2434_;
}
}
v___jp_2783_:
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
lean_inc(v_declName_2371_);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_declName_2371_);
v___x_2792_ = l_instBEqOption_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_a_2790_, v___x_2791_);
lean_dec_ref_known(v___x_2791_, 1);
if (v___x_2792_ == 0)
{
v___y_2679_ = v___y_2786_;
v___y_2680_ = v___y_2787_;
v___y_2681_ = v___y_2788_;
v___y_2682_ = v___y_2789_;
v___y_2683_ = v_a_2790_;
v___y_2684_ = v___y_2785_;
v___y_2685_ = v___y_2784_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2790_);
lean_dec(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2793_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2794_ = l_Lean_MessageData_ofConstName(v_declName_2371_, v___x_2383_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2797_, v___y_2785_, v___y_2784_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
v___jp_2807_:
{
if (lean_obj_tag(v___y_2809_) == 0)
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_box(0);
v___y_2784_ = v___y_2813_;
v___y_2785_ = v___y_2812_;
v___y_2786_ = v___y_2808_;
v___y_2787_ = v___y_2809_;
v___y_2788_ = v_since_x3f_2811_;
v___y_2789_ = v___y_2810_;
v_a_2790_ = v___x_2814_;
goto v___jp_2783_;
}
else
{
lean_object* v_val_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_val_2815_ = lean_ctor_get(v___y_2809_, 0);
v___x_2816_ = lean_box(0);
lean_inc(v_val_2815_);
v___x_2817_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2815_, v___x_2816_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_a_2818_);
v___y_2784_ = v___y_2813_;
v___y_2785_ = v___y_2812_;
v___y_2786_ = v___y_2808_;
v___y_2787_ = v___y_2809_;
v___y_2788_ = v_since_x3f_2811_;
v___y_2789_ = v___y_2810_;
v_a_2790_ = v___x_2819_;
goto v___jp_2783_;
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref_known(v___y_2809_, 1);
lean_dec(v_since_x3f_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v_a_2820_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2817_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2817_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
v___jp_2828_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_unsigned_to_nat(4u);
v___x_2836_ = l_Lean_Syntax_getArg(v_stx_2372_, v___x_2835_);
lean_dec(v_stx_2372_);
v___x_2837_ = l_Lean_Syntax_isNone(v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2836_);
v___x_2839_ = l_Lean_Syntax_matchesNull(v___x_2836_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec(v___x_2836_);
lean_dec(v_typeChanged_x3f_2832_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2840_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2841_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2840_, v___y_2833_, v___y_2834_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = l_Lean_Syntax_getArg(v___x_2836_, v___y_2831_);
lean_dec(v___x_2836_);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
v___y_2808_ = v_typeChanged_x3f_2832_;
v___y_2809_ = v___y_2829_;
v___y_2810_ = v___y_2830_;
v_since_x3f_2811_ = v___x_2843_;
v___y_2812_ = v___y_2833_;
v___y_2813_ = v___y_2834_;
goto v___jp_2807_;
}
}
else
{
lean_object* v___x_2844_; 
lean_dec(v___x_2836_);
v___x_2844_ = lean_box(0);
v___y_2808_ = v_typeChanged_x3f_2832_;
v___y_2809_ = v___y_2829_;
v___y_2810_ = v___y_2830_;
v_since_x3f_2811_ = v___x_2844_;
v___y_2812_ = v___y_2833_;
v___y_2813_ = v___y_2834_;
goto v___jp_2807_;
}
}
v___jp_2845_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(3u);
v___x_2851_ = l_Lean_Syntax_getArg(v_stx_2372_, v___x_2850_);
v___x_2852_ = l_Lean_Syntax_isNone(v___x_2851_);
if (v___x_2852_ == 0)
{
uint8_t v___x_2853_; 
lean_inc(v___x_2851_);
v___x_2853_ = l_Lean_Syntax_matchesNull(v___x_2851_, v___x_2495_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v___x_2851_);
lean_dec(v_text_x3f_2847_);
lean_dec(v___y_2846_);
lean_dec(v_stx_2372_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2854_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2855_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2854_, v___y_2848_, v___y_2849_);
return v___x_2855_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Lean_Syntax_getArg(v___x_2851_, v___x_2494_);
lean_dec(v___x_2851_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
v___y_2829_ = v___y_2846_;
v___y_2830_ = v_text_x3f_2847_;
v___y_2831_ = v___x_2850_;
v_typeChanged_x3f_2832_ = v___x_2857_;
v___y_2833_ = v___y_2848_;
v___y_2834_ = v___y_2849_;
goto v___jp_2828_;
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v___x_2851_);
v___x_2858_ = lean_box(0);
v___y_2829_ = v___y_2846_;
v___y_2830_ = v_text_x3f_2847_;
v___y_2831_ = v___x_2850_;
v_typeChanged_x3f_2832_ = v___x_2858_;
v___y_2833_ = v___y_2848_;
v___y_2834_ = v___y_2849_;
goto v___jp_2828_;
}
}
v___jp_2859_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = lean_unsigned_to_nat(2u);
v___x_2864_ = l_Lean_Syntax_getArg(v_stx_2372_, v___x_2863_);
v___x_2865_ = l_Lean_Syntax_isNone(v___x_2864_);
if (v___x_2865_ == 0)
{
uint8_t v___x_2866_; 
lean_inc(v___x_2864_);
v___x_2866_ = l_Lean_Syntax_matchesNull(v___x_2864_, v___x_2495_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v___x_2864_);
lean_dec(v_id_x3f_2860_);
lean_dec(v_stx_2372_);
lean_dec(v_declName_2371_);
lean_dec_ref(v___x_2369_);
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2366_);
v___x_2867_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2868_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2867_, v___y_2861_, v___y_2862_);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = l_Lean_Syntax_getArg(v___x_2864_, v___x_2494_);
lean_dec(v___x_2864_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___y_2846_ = v_id_x3f_2860_;
v_text_x3f_2847_ = v___x_2870_;
v___y_2848_ = v___y_2861_;
v___y_2849_ = v___y_2862_;
goto v___jp_2845_;
}
}
else
{
lean_object* v___x_2871_; 
lean_dec(v___x_2864_);
v___x_2871_ = lean_box(0);
v___y_2846_ = v_id_x3f_2860_;
v_text_x3f_2847_ = v___x_2871_;
v___y_2848_ = v___y_2861_;
v___y_2849_ = v___y_2862_;
goto v___jp_2845_;
}
}
}
v___jp_2376_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2380_, 0, v___y_2379_);
lean_ctor_set(v___x_2380_, 1, v___y_2377_);
lean_ctor_set(v___x_2380_, 2, v___y_2378_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
v___jp_2384_:
{
if (lean_obj_tag(v___y_2386_) == 0)
{
if (v___x_2383_ == 0)
{
v___y_2377_ = v___y_2385_;
v___y_2378_ = v___y_2386_;
v___y_2379_ = v___y_2387_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2391_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2390_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_dec_ref_known(v___x_2391_, 1);
v___y_2377_ = v___y_2385_;
v___y_2378_ = v___y_2386_;
v___y_2379_ = v___y_2387_;
goto v___jp_2376_;
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v___y_2387_);
lean_dec(v___y_2385_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
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
}
else
{
v___y_2377_ = v___y_2385_;
v___y_2378_ = v___y_2386_;
v___y_2379_ = v___y_2387_;
goto v___jp_2376_;
}
}
v___jp_2400_:
{
if (lean_obj_tag(v___y_2402_) == 0)
{
if (v___x_2383_ == 0)
{
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2406_;
v___y_2387_ = v___y_2405_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
goto v___jp_2384_;
}
else
{
if (lean_obj_tag(v___y_2401_) == 0)
{
if (v___x_2383_ == 0)
{
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2406_;
v___y_2387_ = v___y_2405_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2408_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2407_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_dec_ref_known(v___x_2408_, 1);
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2406_;
v___y_2387_ = v___y_2405_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
else
{
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2406_;
v___y_2387_ = v___y_2405_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
goto v___jp_2384_;
}
}
}
else
{
lean_dec_ref_known(v___y_2402_, 1);
v___y_2385_ = v___y_2401_;
v___y_2386_ = v___y_2406_;
v___y_2387_ = v___y_2405_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
goto v___jp_2384_;
}
}
v___jp_2417_:
{
if (lean_obj_tag(v___y_2421_) == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_box(0);
v___y_2401_ = v___y_2423_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___x_2424_;
goto v___jp_2400_;
}
else
{
lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2433_; 
v_val_2425_ = lean_ctor_get(v___y_2421_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___y_2421_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2427_ = v___y_2421_;
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v___y_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = l_Lean_TSyntax_getString(v_val_2425_);
lean_dec(v_val_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
v___y_2401_ = v___y_2423_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___x_2431_;
goto v___jp_2400_;
}
}
}
}
v___jp_2434_:
{
if (lean_obj_tag(v___y_2436_) == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_box(0);
v___y_2418_ = v___y_2435_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2438_;
v___y_2422_ = v___y_2437_;
v___y_2423_ = v___x_2441_;
goto v___jp_2417_;
}
else
{
lean_object* v_val_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
v_val_2442_ = lean_ctor_get(v___y_2436_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___y_2436_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2444_ = v___y_2436_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_val_2442_);
lean_dec(v___y_2436_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = l_Lean_TSyntax_getString(v_val_2442_);
lean_dec(v_val_2442_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v___y_2418_ = v___y_2435_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2438_;
v___y_2422_ = v___y_2437_;
v___y_2423_ = v___x_2448_;
goto v___jp_2417_;
}
}
}
}
v___jp_2451_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2462_ = l_Lean_ConstantInfo_type(v___y_2452_);
lean_dec_ref(v___y_2452_);
v___x_2463_ = l_Lean_indentExpr(v___x_2462_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2461_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_ConstantInfo_type(v___y_2454_);
lean_dec_ref(v___y_2454_);
v___x_2468_ = l_Lean_indentExpr(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v_hint_2458_);
v___x_2473_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2472_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_dec_ref_known(v___x_2473_, 1);
v___y_2435_ = v___y_2453_;
v___y_2436_ = v___y_2457_;
v___y_2437_ = v___y_2456_;
v___y_2438_ = v___y_2455_;
v___y_2439_ = v___y_2459_;
v___y_2440_ = v___y_2460_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec(v___y_2453_);
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
v___jp_2482_:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___y_2452_ = v___y_2484_;
v___y_2453_ = v___y_2485_;
v___y_2454_ = v___y_2486_;
v___y_2455_ = v___y_2489_;
v___y_2456_ = v___y_2488_;
v___y_2457_ = v___y_2487_;
v_hint_2458_ = v___x_2491_;
v___y_2459_ = v___y_2490_;
v___y_2460_ = v___y_2483_;
goto v___jp_2451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v___f_2882_, lean_object* v___x_2883_, lean_object* v___x_2884_, lean_object* v___x_2885_, lean_object* v_a_2886_, lean_object* v_declName_2887_, lean_object* v_stx_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___x_46793__boxed_2892_; lean_object* v_res_2893_; 
v___x_46793__boxed_2892_ = lean_unbox(v___x_2883_);
v_res_2893_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_2880_, v___x_2881_, v___f_2882_, v___x_46793__boxed_2892_, v___x_2884_, v___x_2885_, v_a_2886_, v_declName_2887_, v_stx_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_a_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2913_; lean_object* v___f_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___f_2920_; lean_object* v___x_2921_; 
v___f_2913_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___f_2914_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2915_ = lean_box(1);
v___x_2916_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_2917_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2918_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2919_ = 0;
v___f_2920_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2921_ = l_Lean_registerParametricAttributeExt___redArg(v___x_2918_, v___x_2919_, v___f_2920_, v___x_2919_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___f_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_n(v_a_2922_, 2);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2924_ = lean_box(v___x_2919_);
v___f_2925_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_2925_, 0, v___x_2917_);
lean_closure_set(v___f_2925_, 1, v___x_2923_);
lean_closure_set(v___f_2925_, 2, v___f_2913_);
lean_closure_set(v___f_2925_, 3, v___x_2924_);
lean_closure_set(v___f_2925_, 4, v___x_2915_);
lean_closure_set(v___f_2925_, 5, v___x_2916_);
lean_closure_set(v___f_2925_, 6, v_a_2922_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2927_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v___f_2925_);
lean_ctor_set(v___x_2927_, 2, v___f_2914_);
lean_ctor_set(v___x_2927_, 3, v___f_2920_);
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*4, v___x_2919_);
v___x_2928_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_2927_, v_a_2922_);
return v___x_2928_;
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_a_2929_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2921_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2921_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2939_, lean_object* v_msg_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_2940_, v___y_2941_, v___y_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_msg_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(v_00_u03b1_2945_, v_msg_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_2951_, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(v_o_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_2961_, lean_object* v_m_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2962_, v_a_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_2965_, lean_object* v_m_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_2965_, v_m_2966_, v_a_2967_);
lean_dec(v_a_2967_);
lean_dec_ref(v_m_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
uint8_t v___x_2972_; 
v___x_2972_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2970_, v_x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
uint8_t v_res_2976_; lean_object* v_r_2977_; 
v_res_2976_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_2973_, v_x_2974_, v_x_2975_);
lean_dec_ref(v_x_2975_);
lean_dec_ref(v_x_2974_);
v_r_2977_ = lean_box(v_res_2976_);
return v_r_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2979_, v_x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2982_, lean_object* v_a_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_2982_, v_a_2983_, v_x_2984_);
lean_dec(v_x_2984_);
lean_dec(v_a_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_2986_, lean_object* v_t_2987_, lean_object* v_k_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_2987_, v_k_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_2990_, lean_object* v_t_2991_, lean_object* v_k_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_2990_, v_t_2991_, v_k_2992_);
lean_dec(v_k_2992_);
lean_dec(v_t_2991_);
return v_res_2993_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2994_, lean_object* v_x_2995_, size_t v_x_2996_, lean_object* v_x_2997_){
_start:
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2995_, v_x_2996_, v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
size_t v_x_48076__boxed_3003_; uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_x_48076__boxed_3003_ = lean_unbox_usize(v_x_3001_);
lean_dec(v_x_3001_);
v_res_3004_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_2999_, v_x_3000_, v_x_48076__boxed_3003_, v_x_3002_);
lean_dec_ref(v_x_3002_);
lean_dec_ref(v_x_3000_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_3006_, uint8_t v_skipAuxDecl_3007_, lean_object* v_auxDeclToFullName_3008_, lean_object* v___x_3009_, lean_object* v_givenNameView_3010_, lean_object* v_as_3011_, lean_object* v_i_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_3006_, v_skipAuxDecl_3007_, v_auxDeclToFullName_3008_, v___x_3009_, v_givenNameView_3010_, v_as_3011_, v_i_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_3015_, lean_object* v_skipAuxDecl_3016_, lean_object* v_auxDeclToFullName_3017_, lean_object* v___x_3018_, lean_object* v_givenNameView_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_a_3022_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3023_; lean_object* v_res_3024_; 
v_skipAuxDecl_boxed_3023_ = lean_unbox(v_skipAuxDecl_3016_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_3015_, v_skipAuxDecl_boxed_3023_, v_auxDeclToFullName_3017_, v___x_3018_, v_givenNameView_3019_, v_as_3020_, v_i_3021_, v_a_3022_);
lean_dec_ref(v_as_3020_);
lean_dec(v_auxDeclToFullName_3017_);
lean_dec(v_givenName_3015_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_3025_, lean_object* v_givenName_3026_, lean_object* v_as_3027_, lean_object* v_i_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_3025_, v_givenName_3026_, v_as_3027_, v_i_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3031_, lean_object* v_givenName_3032_, lean_object* v_as_3033_, lean_object* v_i_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3031_, v_givenName_3032_, v_as_3033_, v_i_3034_, v_a_3035_);
lean_dec_ref(v_as_3033_);
lean_dec(v_givenName_3032_);
lean_dec(v_localDecl_x3f_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3037_, lean_object* v_filter_3038_, lean_object* v_view_x3f_3039_, lean_object* v_as_3040_, lean_object* v_as_x27_3041_, lean_object* v_b_3042_, lean_object* v_a_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3037_, v_filter_3038_, v_view_x3f_3039_, v_as_x27_3041_, v_b_3042_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3050_, lean_object* v_filter_3051_, lean_object* v_view_x3f_3052_, lean_object* v_as_3053_, lean_object* v_as_x27_3054_, lean_object* v_b_3055_, lean_object* v_a_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3050_, v_filter_3051_, v_view_x3f_3052_, v_as_3053_, v_as_x27_3054_, v_b_3055_, v_a_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v_as_x27_3054_);
lean_dec(v_as_3053_);
lean_dec(v_n_u2080_3050_);
return v_res_3062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3063_, lean_object* v_keys_3064_, lean_object* v_vals_3065_, lean_object* v_heq_3066_, lean_object* v_i_3067_, lean_object* v_k_3068_){
_start:
{
uint8_t v___x_3069_; 
v___x_3069_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3064_, v_i_3067_, v_k_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3070_, lean_object* v_keys_3071_, lean_object* v_vals_3072_, lean_object* v_heq_3073_, lean_object* v_i_3074_, lean_object* v_k_3075_){
_start:
{
uint8_t v_res_3076_; lean_object* v_r_3077_; 
v_res_3076_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3070_, v_keys_3071_, v_vals_3072_, v_heq_3073_, v_i_3074_, v_k_3075_);
lean_dec_ref(v_k_3075_);
lean_dec_ref(v_vals_3072_);
lean_dec_ref(v_keys_3071_);
v_r_3077_ = lean_box(v_res_3076_);
return v_r_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3078_, uint8_t v_skipAuxDecl_3079_, lean_object* v_auxDeclToFullName_3080_, lean_object* v___x_3081_, lean_object* v_givenNameView_3082_, lean_object* v_as_3083_, lean_object* v_i_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3078_, v_skipAuxDecl_3079_, v_auxDeclToFullName_3080_, v___x_3081_, v_givenNameView_3082_, v_as_3083_, v_i_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3087_, lean_object* v_skipAuxDecl_3088_, lean_object* v_auxDeclToFullName_3089_, lean_object* v___x_3090_, lean_object* v_givenNameView_3091_, lean_object* v_as_3092_, lean_object* v_i_3093_, lean_object* v_a_3094_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3095_; lean_object* v_res_3096_; 
v_skipAuxDecl_boxed_3095_ = lean_unbox(v_skipAuxDecl_3088_);
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3087_, v_skipAuxDecl_boxed_3095_, v_auxDeclToFullName_3089_, v___x_3090_, v_givenNameView_3091_, v_as_3092_, v_i_3093_, v_a_3094_);
lean_dec_ref(v_as_3092_);
lean_dec(v_auxDeclToFullName_3089_);
lean_dec(v_givenName_3087_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3097_, lean_object* v_givenName_3098_, lean_object* v_as_3099_, lean_object* v_i_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3097_, v_givenName_3098_, v_as_3099_, v_i_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3103_, lean_object* v_givenName_3104_, lean_object* v_as_3105_, lean_object* v_i_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3103_, v_givenName_3104_, v_as_3105_, v_i_3106_, v_a_3107_);
lean_dec_ref(v_as_3105_);
lean_dec(v_givenName_3104_);
lean_dec(v_localDecl_x3f_3103_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3109_, v___y_3112_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v_opt_3116_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3123_, v___y_3126_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v_opt_3130_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3137_, lean_object* v_entry_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_env_3142_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = l_Lean_Linter_deprecatedAttr;
v___x_3144_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3143_, v_env_3142_, v_declName_3137_, v_entry_3138_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_inst_3141_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3154_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 3);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = l_Lean_MessageData_ofFormat(v___x_3150_);
v___x_3152_ = l_Lean_throwError___redArg(v_inst_3139_, v_inst_3140_, v___x_3151_);
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3156_; 
lean_dec_ref(v_inst_3140_);
lean_dec_ref(v_inst_3139_);
v_a_3155_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3156_ = l_Lean_setEnv___redArg(v_inst_3141_, v_a_3155_);
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_declName_3160_, lean_object* v_entry_3161_){
_start:
{
lean_object* v_toBind_3162_; lean_object* v_getEnv_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; 
v_toBind_3162_ = lean_ctor_get(v_inst_3157_, 1);
lean_inc(v_toBind_3162_);
v_getEnv_3163_ = lean_ctor_get(v_inst_3158_, 0);
lean_inc(v_getEnv_3163_);
v___f_3164_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3164_, 0, v_declName_3160_);
lean_closure_set(v___f_3164_, 1, v_entry_3161_);
lean_closure_set(v___f_3164_, 2, v_inst_3157_);
lean_closure_set(v___f_3164_, 3, v_inst_3159_);
lean_closure_set(v___f_3164_, 4, v_inst_3158_);
v___x_3165_ = lean_apply_4(v_toBind_3162_, lean_box(0), lean_box(0), v_getEnv_3163_, v___f_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_declName_3170_, lean_object* v_entry_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3167_, v_inst_3168_, v_inst_3169_, v_declName_3170_, v_entry_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3173_, lean_object* v_declName_3174_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3176_ = l_Lean_Linter_deprecatedAttr;
v___x_3177_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3175_, v___x_3176_, v_env_3173_, v_declName_3174_);
if (lean_obj_tag(v___x_3177_) == 0)
{
uint8_t v___x_3178_; 
v___x_3178_ = 0;
return v___x_3178_;
}
else
{
uint8_t v___x_3179_; 
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = 1;
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3180_, lean_object* v_declName_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_Linter_isDeprecated(v_env_3180_, v_declName_3181_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3184_){
_start:
{
lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3186_ = lean_name_eq(v_x_3184_, v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3187_){
_start:
{
uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_res_3188_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3187_);
lean_dec(v_x_3187_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3191_){
_start:
{
lean_object* v___f_3192_; uint8_t v___x_3193_; 
v___f_3192_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3193_ = l_Lean_MessageData_hasTag(v___f_3192_, v_msg_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3194_){
_start:
{
uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_res_3195_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3194_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3197_, lean_object* v_declName_3198_){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3200_ = l_Lean_Linter_deprecatedAttr;
v___x_3201_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3199_, v___x_3200_, v_env_3197_, v_declName_3198_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_box(0);
return v___x_3202_;
}
else
{
lean_object* v_val_3203_; lean_object* v_newName_x3f_3204_; 
v_val_3203_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v___x_3201_, 1);
v_newName_x3f_3204_ = lean_ctor_get(v_val_3203_, 0);
lean_inc(v_newName_x3f_3204_);
lean_dec(v_val_3203_);
return v_newName_x3f_3204_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 0)
{
if (lean_obj_tag(v_x_3206_) == 0)
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
return v___x_3207_;
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
return v___x_3208_;
}
}
else
{
if (lean_obj_tag(v_x_3206_) == 0)
{
uint8_t v___x_3209_; 
v___x_3209_ = 0;
return v___x_3209_;
}
else
{
lean_object* v_head_3210_; lean_object* v_tail_3211_; lean_object* v_head_3212_; lean_object* v_tail_3213_; uint8_t v___x_3214_; 
v_head_3210_ = lean_ctor_get(v_x_3205_, 0);
v_tail_3211_ = lean_ctor_get(v_x_3205_, 1);
v_head_3212_ = lean_ctor_get(v_x_3206_, 0);
v_tail_3213_ = lean_ctor_get(v_x_3206_, 1);
v___x_3214_ = lean_string_dec_eq(v_head_3210_, v_head_3212_);
if (v___x_3214_ == 0)
{
return v___x_3214_;
}
else
{
v_x_3205_ = v_tail_3211_;
v_x_3206_ = v_tail_3213_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3216_, v_x_3217_);
lean_dec(v_x_3217_);
lean_dec(v_x_3216_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3220_, lean_object* v_x_3221_){
_start:
{
if (lean_obj_tag(v_x_3220_) == 0)
{
if (lean_obj_tag(v_x_3221_) == 0)
{
uint8_t v___x_3222_; 
v___x_3222_ = 1;
return v___x_3222_;
}
else
{
uint8_t v___x_3223_; 
v___x_3223_ = 0;
return v___x_3223_;
}
}
else
{
if (lean_obj_tag(v_x_3221_) == 0)
{
uint8_t v___x_3224_; 
v___x_3224_ = 0;
return v___x_3224_;
}
else
{
lean_object* v_head_3225_; lean_object* v_tail_3226_; lean_object* v_head_3227_; lean_object* v_tail_3228_; uint8_t v___y_3230_; lean_object* v_fst_3232_; lean_object* v_snd_3233_; lean_object* v_fst_3234_; lean_object* v_snd_3235_; uint8_t v___x_3236_; 
v_head_3225_ = lean_ctor_get(v_x_3220_, 0);
v_tail_3226_ = lean_ctor_get(v_x_3220_, 1);
v_head_3227_ = lean_ctor_get(v_x_3221_, 0);
v_tail_3228_ = lean_ctor_get(v_x_3221_, 1);
v_fst_3232_ = lean_ctor_get(v_head_3225_, 0);
v_snd_3233_ = lean_ctor_get(v_head_3225_, 1);
v_fst_3234_ = lean_ctor_get(v_head_3227_, 0);
v_snd_3235_ = lean_ctor_get(v_head_3227_, 1);
v___x_3236_ = lean_name_eq(v_fst_3232_, v_fst_3234_);
if (v___x_3236_ == 0)
{
v___y_3230_ = v___x_3236_;
goto v___jp_3229_;
}
else
{
uint8_t v___x_3237_; 
v___x_3237_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3233_, v_snd_3235_);
v___y_3230_ = v___x_3237_;
goto v___jp_3229_;
}
v___jp_3229_:
{
if (v___y_3230_ == 0)
{
return v___y_3230_;
}
else
{
v_x_3220_ = v_tail_3226_;
v_x_3221_ = v_tail_3228_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
uint8_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3238_, v_x_3239_);
lean_dec(v_x_3239_);
lean_dec(v_x_3238_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3245_, lean_object* v_newName_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_ref_3252_; 
v_ref_3252_ = lean_ctor_get(v_a_3249_, 2);
if (lean_obj_tag(v_ref_3252_) == 3)
{
lean_object* v_val_3253_; uint8_t v___x_3254_; 
v_val_3253_ = lean_ctor_get(v_ref_3252_, 2);
v___x_3254_ = l_Lean_Name_hasMacroScopes(v_val_3253_);
if (v___x_3254_ == 0)
{
uint8_t v___x_3255_; lean_object* v___x_3333_; 
v___x_3255_ = 1;
v___x_3333_ = l_Lean_Syntax_getRange_x3f(v_ref_3252_, v___x_3255_);
if (lean_obj_tag(v___x_3333_) == 0)
{
if (v___x_3254_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v_newName_3246_);
lean_dec(v_declName_3245_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
else
{
goto v___jp_3256_;
}
}
else
{
lean_dec_ref_known(v___x_3333_, 1);
goto v___jp_3256_;
}
v___jp_3256_:
{
lean_object* v___x_3257_; 
lean_inc(v_val_3253_);
v___x_3257_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3253_, v___x_3255_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3324_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3324_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3324_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v_declName_3245_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
lean_ctor_set(v___x_3264_, 1, v___x_3262_);
v___x_3265_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3258_, v___x_3264_);
lean_dec_ref_known(v___x_3264_, 2);
lean_dec(v_a_3258_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_dec(v_newName_3246_);
v___x_3266_ = lean_box(0);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3266_);
v___x_3268_ = v___x_3260_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
else
{
lean_object* v___x_3270_; 
lean_del_object(v___x_3260_);
v___x_3270_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_newName_3246_, v___x_3254_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3315_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3315_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3315_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
if (lean_obj_tag(v_a_3271_) == 1)
{
lean_object* v_val_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3310_; 
lean_del_object(v___x_3273_);
v_val_3275_ = lean_ctor_get(v_a_3271_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_a_3271_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3277_ = v_a_3271_;
v_isShared_3278_ = v_isSharedCheck_3310_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_val_3275_);
lean_dec(v_a_3271_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3310_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3279_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3280_ = l_Lean_Name_toString(v_val_3275_, v___x_3255_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
lean_ctor_set(v___x_3283_, 2, v___x_3282_);
lean_ctor_set(v___x_3283_, 3, v___x_3282_);
lean_ctor_set(v___x_3283_, 4, v___x_3282_);
lean_ctor_set(v___x_3283_, 5, v___x_3282_);
v___x_3284_ = 0;
v___x_3285_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3282_);
lean_ctor_set(v___x_3285_, 2, v___x_3282_);
lean_ctor_set_uint8(v___x_3285_, sizeof(void*)*3, v___x_3284_);
v___x_3286_ = lean_unsigned_to_nat(1u);
v___x_3287_ = lean_mk_empty_array_with_capacity(v___x_3286_);
v___x_3288_ = lean_array_push(v___x_3287_, v___x_3285_);
lean_inc_ref(v_ref_3252_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v_ref_3252_);
v___x_3290_ = v___x_3277_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_ref_3252_);
v___x_3290_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_MessageData_hint(v___x_3279_, v___x_3288_, v___x_3290_, v___x_3282_, v___x_3254_, v_a_3249_, v_a_3250_);
lean_dec_ref(v___x_3288_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3300_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3300_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3300_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_a_3292_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v___x_3296_);
v___x_3298_ = v___x_3294_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
v_a_3301_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3291_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3291_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_dec(v_a_3271_);
v___x_3311_ = lean_box(0);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3311_);
v___x_3313_ = v___x_3273_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
v_a_3316_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3270_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3270_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_newName_3246_);
lean_dec(v_declName_3245_);
v_a_3325_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3257_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3257_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec(v_newName_3246_);
lean_dec(v_declName_3245_);
v___x_3336_ = lean_box(0);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v_newName_3246_);
lean_dec(v_declName_3245_);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3340_, lean_object* v_newName_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3340_, v_newName_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_env_3353_; lean_object* v___x_3354_; lean_object* v_toEnvExtension_3355_; lean_object* v_asyncMode_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v_merged_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3368_; 
v___x_3351_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3352_ = lean_st_ref_get(v___y_3349_);
v_env_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_ref(v_env_3353_);
lean_dec(v___x_3352_);
v___x_3354_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3355_ = lean_ctor_get(v___x_3354_, 0);
v_asyncMode_3356_ = lean_ctor_get(v_toEnvExtension_3355_, 2);
v___x_3357_ = lean_box(0);
v___x_3358_ = 0;
v___x_3359_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3351_, v___x_3354_, v_env_3353_, v_asyncMode_3356_, v___x_3357_, v___x_3358_);
v_merged_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3359_, 1);
lean_dec(v_unused_3369_);
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3368_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_merged_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3368_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v_merged_3360_);
lean_ctor_set(v___x_3362_, 0, v_o_3348_);
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_o_3348_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_merged_3360_);
v___x_3365_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3370_, v___y_3371_);
lean_dec(v___y_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3376_);
v___x_3380_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v___x_3379_, v___y_3377_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3386_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3389_ = l_Lean_stringToMessageData(v___x_3388_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3392_ = l_Lean_stringToMessageData(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3411_ = l_Lean_MessageData_ofFormat(v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3430_, uint8_t v_allowSuggestion_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3610_; 
v___x_3437_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3438_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3610_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3610_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; uint8_t v___x_3444_; lean_object* v_extraMsg_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; 
v___x_3443_ = l_Lean_Linter_linter_deprecated;
v___x_3444_ = l_Lean_Linter_getLinterValue(v___x_3443_, v_a_3439_);
lean_dec(v_a_3439_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
lean_dec(v_declName_3430_);
v___x_3460_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3460_);
v___x_3462_ = v___x_3441_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
else
{
lean_object* v___x_3464_; lean_object* v_env_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3464_ = lean_st_ref_get(v_a_3435_);
v_env_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc_ref(v_env_3465_);
lean_dec(v___x_3464_);
v___x_3466_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3430_);
v___x_3467_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3437_, v___x_3466_, v_env_3465_, v_declName_3430_);
if (lean_obj_tag(v___x_3467_) == 1)
{
lean_object* v_val_3468_; lean_object* v_text_x3f_3469_; 
lean_del_object(v___x_3441_);
v_val_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v_text_x3f_3469_ = lean_ctor_get(v_val_3468_, 1);
if (lean_obj_tag(v_text_x3f_3469_) == 0)
{
lean_object* v_newName_x3f_3470_; 
v_newName_x3f_3470_ = lean_ctor_get(v_val_3468_, 0);
lean_inc(v_newName_x3f_3470_);
lean_dec(v_val_3468_);
if (lean_obj_tag(v_newName_x3f_3470_) == 0)
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v_extraMsg_3446_ = v___x_3471_;
v___y_3447_ = v_a_3432_;
v___y_3448_ = v_a_3433_;
v___y_3449_ = v_a_3434_;
v___y_3450_ = v_a_3435_;
goto v___jp_3445_;
}
else
{
lean_object* v_val_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v_env_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; 
v_val_3472_ = lean_ctor_get(v_newName_x3f_3470_, 0);
lean_inc_n(v_val_3472_, 2);
lean_dec_ref_known(v_newName_x3f_3470_, 1);
v___x_3473_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3474_ = l_Lean_MessageData_ofConstName(v_val_3472_, v___x_3444_);
lean_inc_ref(v___x_3474_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_st_ref_get(v_a_3435_);
v_env_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc_ref_n(v_env_3479_, 2);
lean_dec(v___x_3478_);
v___x_3480_ = l_Lean_Name_getPrefix(v_declName_3430_);
v___x_3481_ = 0;
lean_inc(v_declName_3430_);
v___x_3482_ = l_Lean_Environment_find_x3f(v_env_3479_, v_declName_3430_, v___x_3481_);
if (lean_obj_tag(v___x_3482_) == 1)
{
lean_object* v_val_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_val_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = l_Lean_Name_getPrefix(v_val_3472_);
lean_inc(v_val_3472_);
lean_inc_ref(v_env_3479_);
v___x_3485_ = l_Lean_Environment_find_x3f(v_env_3479_, v_val_3472_, v___x_3481_);
if (lean_obj_tag(v___x_3485_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3487_; 
v_val_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3483_, v_val_3486_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v_msg_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v_msg_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; uint8_t v___x_3582_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3582_ = lean_unbox(v_a_3488_);
if (v___x_3582_ == 0)
{
if (v___x_3444_ == 0)
{
lean_dec(v_val_3486_);
lean_dec(v_val_3483_);
v_msg_3575_ = v___x_3477_;
v___y_3576_ = v_a_3432_;
v___y_3577_ = v_a_3433_;
v___y_3578_ = v_a_3434_;
v___y_3579_ = v_a_3435_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3583_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3584_ = l_Lean_ConstantInfo_type(v_val_3486_);
lean_dec(v_val_3486_);
v___x_3585_ = l_Lean_indentExpr(v___x_3584_);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3583_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = l_Lean_ConstantInfo_type(v_val_3483_);
lean_dec(v_val_3483_);
v___x_3590_ = l_Lean_indentExpr(v___x_3589_);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3588_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Lean_MessageData_note(v___x_3591_);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3477_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v_msg_3575_ = v___x_3593_;
v___y_3576_ = v_a_3432_;
v___y_3577_ = v_a_3433_;
v___y_3578_ = v_a_3434_;
v___y_3579_ = v_a_3435_;
goto v___jp_3574_;
}
}
else
{
lean_dec(v_val_3486_);
lean_dec(v_val_3483_);
v_msg_3575_ = v___x_3477_;
v___y_3576_ = v_a_3432_;
v___y_3577_ = v_a_3433_;
v___y_3578_ = v_a_3434_;
v___y_3579_ = v_a_3435_;
goto v___jp_3574_;
}
v___jp_3489_:
{
if (v_allowSuggestion_3431_ == 0)
{
lean_dec(v_a_3488_);
lean_dec(v_val_3472_);
v_extraMsg_3446_ = v_msg_3490_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3492_;
v___y_3449_ = v___y_3493_;
v___y_3450_ = v___y_3494_;
goto v___jp_3445_;
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_unbox(v_a_3488_);
lean_dec(v_a_3488_);
if (v___x_3495_ == 0)
{
lean_dec(v_val_3472_);
v_extraMsg_3446_ = v_msg_3490_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3492_;
v___y_3449_ = v___y_3493_;
v___y_3450_ = v___y_3494_;
goto v___jp_3445_;
}
else
{
lean_object* v___x_3496_; 
lean_inc(v_declName_3430_);
v___x_3496_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3430_, v_val_3472_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3498_; lean_object* v___x_3499_; 
v_val_3498_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3497_, 1);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v_msg_3490_);
lean_ctor_set(v___x_3499_, 1, v_val_3498_);
v_extraMsg_3446_ = v___x_3499_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3492_;
v___y_3449_ = v___y_3493_;
v___y_3450_ = v___y_3494_;
goto v___jp_3445_;
}
else
{
lean_dec(v_a_3497_);
v_extraMsg_3446_ = v_msg_3490_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3492_;
v___y_3449_ = v___y_3493_;
v___y_3450_ = v___y_3494_;
goto v___jp_3445_;
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v_msg_3490_);
lean_dec(v_declName_3430_);
v_a_3500_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3496_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3496_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
}
v___jp_3508_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3515_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
lean_ctor_set(v___x_3516_, 1, v___x_3474_);
v___x_3517_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___y_3514_);
v___x_3520_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_ofName(v___x_3484_);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_MessageData_note(v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___y_3513_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v_msg_3490_ = v___x_3527_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3511_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3512_;
goto v___jp_3489_;
}
v___jp_3528_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3535_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___y_3534_);
v___x_3537_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_MessageData_note(v___x_3538_);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___y_3533_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v_msg_3490_ = v___x_3540_;
v___y_3491_ = v___y_3529_;
v___y_3492_ = v___y_3531_;
v___y_3493_ = v___y_3530_;
v___y_3494_ = v___y_3532_;
goto v___jp_3489_;
}
v___jp_3541_:
{
if (v___y_3548_ == 0)
{
uint8_t v___x_3549_; 
lean_inc(v_declName_3430_);
lean_inc_ref(v_env_3479_);
v___x_3549_ = l_Lean_isProtected(v_env_3479_, v_declName_3430_);
if (v___x_3549_ == 0)
{
if (v___x_3444_ == 0)
{
lean_dec(v___x_3484_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
v_msg_3490_ = v___y_3547_;
v___y_3491_ = v___y_3542_;
v___y_3492_ = v___y_3544_;
v___y_3493_ = v___y_3543_;
v___y_3494_ = v___y_3546_;
goto v___jp_3489_;
}
else
{
uint8_t v___x_3550_; 
lean_inc(v_val_3472_);
v___x_3550_ = l_Lean_isProtected(v_env_3479_, v_val_3472_);
if (v___x_3550_ == 0)
{
lean_dec(v___x_3484_);
lean_dec_ref(v___x_3474_);
v_msg_3490_ = v___y_3547_;
v___y_3491_ = v___y_3542_;
v___y_3492_ = v___y_3544_;
v___y_3493_ = v___y_3543_;
v___y_3494_ = v___y_3546_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
lean_inc(v___x_3484_);
v___x_3551_ = l_Lean_Name_componentsRev(v___x_3484_);
v___x_3552_ = lean_unsigned_to_nat(1u);
v___x_3553_ = l_List_lengthTR___redArg(v___x_3551_);
v___x_3554_ = lean_nat_dec_lt(v___x_3552_, v___x_3553_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec(v___x_3551_);
v___x_3555_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3509_ = v___y_3542_;
v___y_3510_ = v___y_3543_;
v___y_3511_ = v___y_3544_;
v___y_3512_ = v___y_3546_;
v___y_3513_ = v___y_3547_;
v___y_3514_ = v___x_3555_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3556_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = l_List_get___redArg(v___x_3551_, v___x_3557_);
lean_dec(v___x_3551_);
v___x_3559_ = l_Lean_MessageData_ofName(v___x_3558_);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3556_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___y_3509_ = v___y_3542_;
v___y_3510_ = v___y_3543_;
v___y_3511_ = v___y_3544_;
v___y_3512_ = v___y_3546_;
v___y_3513_ = v___y_3547_;
v___y_3514_ = v___x_3562_;
goto v___jp_3508_;
}
}
}
}
else
{
lean_dec(v___x_3484_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
v_msg_3490_ = v___y_3547_;
v___y_3491_ = v___y_3542_;
v___y_3492_ = v___y_3544_;
v___y_3493_ = v___y_3543_;
v___y_3494_ = v___y_3546_;
goto v___jp_3489_;
}
}
else
{
lean_dec(v___x_3484_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
if (lean_obj_tag(v_declName_3430_) == 1)
{
lean_object* v_str_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v_str_3563_ = lean_ctor_get(v_declName_3430_, 1);
v___x_3564_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3563_);
v___x_3565_ = l_Lean_stringToMessageData(v_str_3563_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
lean_inc(v_val_3472_);
v___x_3569_ = l_Lean_MessageData_ofConstName(v_val_3472_, v___y_3545_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___y_3529_ = v___y_3542_;
v___y_3530_ = v___y_3543_;
v___y_3531_ = v___y_3544_;
v___y_3532_ = v___y_3546_;
v___y_3533_ = v___y_3547_;
v___y_3534_ = v___x_3572_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_MessageData_nil;
v___y_3529_ = v___y_3542_;
v___y_3530_ = v___y_3543_;
v___y_3531_ = v___y_3544_;
v___y_3532_ = v___y_3546_;
v___y_3533_ = v___y_3547_;
v___y_3534_ = v___x_3573_;
goto v___jp_3528_;
}
}
}
v___jp_3574_:
{
uint8_t v___x_3580_; 
v___x_3580_ = l_Lean_Name_isAnonymous(v___x_3480_);
if (v___x_3580_ == 0)
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_name_eq(v___x_3480_, v___x_3484_);
lean_dec(v___x_3480_);
if (v___x_3581_ == 0)
{
v___y_3542_ = v___y_3576_;
v___y_3543_ = v___y_3578_;
v___y_3544_ = v___y_3577_;
v___y_3545_ = v___x_3580_;
v___y_3546_ = v___y_3579_;
v___y_3547_ = v_msg_3575_;
v___y_3548_ = v___x_3444_;
goto v___jp_3541_;
}
else
{
v___y_3542_ = v___y_3576_;
v___y_3543_ = v___y_3578_;
v___y_3544_ = v___y_3577_;
v___y_3545_ = v___x_3580_;
v___y_3546_ = v___y_3579_;
v___y_3547_ = v_msg_3575_;
v___y_3548_ = v___x_3580_;
goto v___jp_3541_;
}
}
else
{
lean_dec(v___x_3484_);
lean_dec(v___x_3480_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
v_msg_3490_ = v_msg_3575_;
v___y_3491_ = v___y_3576_;
v___y_3492_ = v___y_3577_;
v___y_3493_ = v___y_3578_;
v___y_3494_ = v___y_3579_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_val_3486_);
lean_dec(v___x_3484_);
lean_dec(v_val_3483_);
lean_dec(v___x_3480_);
lean_dec_ref(v_env_3479_);
lean_dec_ref_known(v___x_3477_, 2);
lean_dec_ref(v___x_3474_);
lean_dec(v_val_3472_);
lean_dec(v_declName_3430_);
v_a_3594_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3487_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3487_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_dec(v___x_3485_);
lean_dec(v___x_3484_);
lean_dec(v_val_3483_);
lean_dec(v___x_3480_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
lean_dec(v_val_3472_);
v_extraMsg_3446_ = v___x_3477_;
v___y_3447_ = v_a_3432_;
v___y_3448_ = v_a_3433_;
v___y_3449_ = v_a_3434_;
v___y_3450_ = v_a_3435_;
goto v___jp_3445_;
}
}
else
{
lean_dec(v___x_3482_);
lean_dec(v___x_3480_);
lean_dec_ref(v_env_3479_);
lean_dec_ref(v___x_3474_);
lean_dec(v_val_3472_);
v_extraMsg_3446_ = v___x_3477_;
v___y_3447_ = v_a_3432_;
v___y_3448_ = v_a_3433_;
v___y_3449_ = v_a_3434_;
v___y_3450_ = v_a_3435_;
goto v___jp_3445_;
}
}
}
else
{
lean_object* v_val_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
lean_inc_ref(v_text_x3f_3469_);
lean_dec(v_val_3468_);
v_val_3602_ = lean_ctor_get(v_text_x3f_3469_, 0);
lean_inc(v_val_3602_);
lean_dec_ref_known(v_text_x3f_3469_, 1);
v___x_3603_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3604_ = l_Lean_stringToMessageData(v_val_3602_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v_extraMsg_3446_ = v___x_3605_;
v___y_3447_ = v_a_3432_;
v___y_3448_ = v_a_3433_;
v___y_3449_ = v_a_3434_;
v___y_3450_ = v_a_3435_;
goto v___jp_3445_;
}
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
lean_dec(v___x_3467_);
lean_dec(v_declName_3430_);
v___x_3606_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3606_);
v___x_3608_ = v___x_3441_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
v___jp_3445_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3451_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3452_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3453_ = l_Lean_MessageData_ofConstName(v_declName_3430_, v___x_3444_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v_extraMsg_3446_);
v___x_3458_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3451_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_3458_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3611_, lean_object* v_allowSuggestion_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
uint8_t v_allowSuggestion_boxed_3618_; lean_object* v_res_3619_; 
v_allowSuggestion_boxed_3618_ = lean_unbox(v_allowSuggestion_3612_);
v_res_3619_ = l_Lean_Linter_checkDeprecated(v_declName_3611_, v_allowSuggestion_boxed_3618_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3620_, v___y_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3633_;
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
