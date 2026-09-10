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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
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
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__3_value;
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
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Deprecate in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` instead:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(uint8_t v___x_193_, lean_object* v_env_194_, lean_object* v_n_195_, lean_object* v_x_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Environment_contains(v_env_194_, v_n_195_, v___x_193_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_198_, lean_object* v_env_199_, lean_object* v_n_200_, lean_object* v_x_201_){
_start:
{
uint8_t v___x_43008__boxed_202_; uint8_t v_res_203_; lean_object* v_r_204_; 
v___x_43008__boxed_202_ = lean_unbox(v___x_198_);
v_res_203_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_43008__boxed_202_, v_env_199_, v_n_200_, v_x_201_);
lean_dec_ref(v_x_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_208_);
lean_dec_ref(v_x_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_217_, v_x_218_, v_x_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v_x_219_);
lean_dec_ref(v_x_218_);
lean_dec(v_x_217_);
return v_res_222_;
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
uint8_t v_suppressElabErrors_boxed_301_; uint8_t v___y_43117__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_suppressElabErrors_boxed_301_ = lean_unbox(v_suppressElabErrors_298_);
v___y_43117__boxed_302_ = lean_unbox(v___y_299_);
v_res_303_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_301_, v___y_43117__boxed_302_, v_x_300_);
lean_dec(v_x_300_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_306_, lean_object* v_msgData_307_, uint8_t v_severity_308_, uint8_t v_isSilent_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_353_; uint8_t v___y_354_; uint8_t v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_378_; uint8_t v___y_379_; uint8_t v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_389_; uint8_t v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; uint8_t v___y_395_; uint8_t v___x_400_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; uint8_t v___y_405_; uint8_t v___y_406_; lean_object* v___y_407_; uint8_t v___y_408_; uint8_t v___y_410_; uint8_t v___x_426_; 
v___x_400_ = 2;
v___x_426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_308_, v___x_400_);
if (v___x_426_ == 0)
{
v___y_410_ = v___x_426_;
goto v___jp_409_;
}
else
{
uint8_t v___x_427_; 
lean_inc_ref(v_msgData_307_);
v___x_427_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_307_);
v___y_410_ = v___x_427_;
goto v___jp_409_;
}
v___jp_315_:
{
lean_object* v___x_325_; lean_object* v_toCold_326_; lean_object* v_currNamespace_327_; lean_object* v_openDecls_328_; lean_object* v_env_329_; lean_object* v_nextMacroScope_330_; lean_object* v_ngen_331_; lean_object* v_auxDeclNGen_332_; lean_object* v_traceState_333_; lean_object* v_cache_334_; lean_object* v_messages_335_; lean_object* v_infoState_336_; lean_object* v_snapshotTasks_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_351_; 
v___x_325_ = lean_st_ref_take(v___y_324_);
v_toCold_326_ = lean_ctor_get(v___y_323_, 0);
v_currNamespace_327_ = lean_ctor_get(v_toCold_326_, 4);
v_openDecls_328_ = lean_ctor_get(v_toCold_326_, 5);
v_env_329_ = lean_ctor_get(v___x_325_, 0);
v_nextMacroScope_330_ = lean_ctor_get(v___x_325_, 1);
v_ngen_331_ = lean_ctor_get(v___x_325_, 2);
v_auxDeclNGen_332_ = lean_ctor_get(v___x_325_, 3);
v_traceState_333_ = lean_ctor_get(v___x_325_, 4);
v_cache_334_ = lean_ctor_get(v___x_325_, 5);
v_messages_335_ = lean_ctor_get(v___x_325_, 6);
v_infoState_336_ = lean_ctor_get(v___x_325_, 7);
v_snapshotTasks_337_ = lean_ctor_get(v___x_325_, 8);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_351_ == 0)
{
v___x_339_ = v___x_325_;
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snapshotTasks_337_);
lean_inc(v_infoState_336_);
lean_inc(v_messages_335_);
lean_inc(v_cache_334_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_332_);
lean_inc(v_ngen_331_);
lean_inc(v_nextMacroScope_330_);
lean_inc(v_env_329_);
lean_dec(v___x_325_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc(v_openDecls_328_);
lean_inc(v_currNamespace_327_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_currNamespace_327_);
lean_ctor_set(v___x_341_, 1, v_openDecls_328_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___y_321_);
lean_inc_ref(v___y_318_);
lean_inc_ref(v___y_322_);
v___x_343_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_343_, 0, v___y_322_);
lean_ctor_set(v___x_343_, 1, v___y_320_);
lean_ctor_set(v___x_343_, 2, v___y_316_);
lean_ctor_set(v___x_343_, 3, v___y_318_);
lean_ctor_set(v___x_343_, 4, v___x_342_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*5, v___y_319_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*5 + 1, v___y_317_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*5 + 2, v_isSilent_309_);
v___x_344_ = l_Lean_MessageLog_add(v___x_343_, v_messages_335_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 6, v___x_344_);
v___x_346_ = v___x_339_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_env_329_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_nextMacroScope_330_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_ngen_331_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_auxDeclNGen_332_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_traceState_333_);
lean_ctor_set(v_reuseFailAlloc_350_, 5, v_cache_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 6, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_350_, 7, v_infoState_336_);
lean_ctor_set(v_reuseFailAlloc_350_, 8, v_snapshotTasks_337_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_st_ref_put(v___y_324_, v___x_346_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
v___jp_352_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_376_; 
v___x_361_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_307_);
v___x_362_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_361_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_376_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_376_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_376_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
lean_inc_ref_n(v___y_357_, 2);
v___x_367_ = l_Lean_FileMap_toPosition(v___y_357_, v___y_358_);
lean_dec(v___y_358_);
v___x_368_ = l_Lean_FileMap_toPosition(v___y_357_, v___y_360_);
lean_dec(v___y_360_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
v___x_370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_354_ == 0)
{
lean_del_object(v___x_365_);
lean_dec_ref(v___y_353_);
v___y_316_ = v___x_369_;
v___y_317_ = v___y_355_;
v___y_318_ = v___x_370_;
v___y_319_ = v___y_356_;
v___y_320_ = v___x_367_;
v___y_321_ = v_a_363_;
v___y_322_ = v___y_359_;
v___y_323_ = v___y_312_;
v___y_324_ = v___y_313_;
goto v___jp_315_;
}
else
{
uint8_t v___x_371_; 
lean_inc(v_a_363_);
v___x_371_ = l_Lean_MessageData_hasTag(v___y_353_, v_a_363_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec_ref_known(v___x_369_, 1);
lean_dec_ref(v___x_367_);
lean_dec(v_a_363_);
v___x_372_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_372_);
v___x_374_ = v___x_365_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_del_object(v___x_365_);
v___y_316_ = v___x_369_;
v___y_317_ = v___y_355_;
v___y_318_ = v___x_370_;
v___y_319_ = v___y_356_;
v___y_320_ = v___x_367_;
v___y_321_ = v_a_363_;
v___y_322_ = v___y_359_;
v___y_323_ = v___y_312_;
v___y_324_ = v___y_313_;
goto v___jp_315_;
}
}
}
}
v___jp_377_:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Syntax_getTailPos_x3f(v___y_383_, v___y_381_);
lean_dec(v___y_383_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_inc(v___y_385_);
v___y_353_ = v___y_378_;
v___y_354_ = v___y_379_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___y_382_;
v___y_358_ = v___y_385_;
v___y_359_ = v___y_384_;
v___y_360_ = v___y_385_;
goto v___jp_352_;
}
else
{
lean_object* v_val_387_; 
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_386_, 1);
v___y_353_ = v___y_378_;
v___y_354_ = v___y_379_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___y_382_;
v___y_358_ = v___y_385_;
v___y_359_ = v___y_384_;
v___y_360_ = v_val_387_;
goto v___jp_352_;
}
}
v___jp_388_:
{
lean_object* v_ref_396_; lean_object* v___x_397_; 
v_ref_396_ = l_Lean_replaceRef(v_ref_306_, v___y_392_);
v___x_397_ = l_Lean_Syntax_getPos_x3f(v_ref_396_, v___y_391_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___y_378_ = v___y_389_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_395_;
v___y_381_ = v___y_391_;
v___y_382_ = v___y_393_;
v___y_383_ = v_ref_396_;
v___y_384_ = v___y_394_;
v___y_385_ = v___x_398_;
goto v___jp_377_;
}
else
{
lean_object* v_val_399_; 
v_val_399_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v___x_397_, 1);
v___y_378_ = v___y_389_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_395_;
v___y_381_ = v___y_391_;
v___y_382_ = v___y_393_;
v___y_383_ = v_ref_396_;
v___y_384_ = v___y_394_;
v___y_385_ = v_val_399_;
goto v___jp_377_;
}
}
v___jp_401_:
{
if (v___y_408_ == 0)
{
v___y_389_ = v___y_402_;
v___y_390_ = v___y_405_;
v___y_391_ = v___y_406_;
v___y_392_ = v___y_407_;
v___y_393_ = v___y_403_;
v___y_394_ = v___y_404_;
v___y_395_ = v_severity_308_;
goto v___jp_388_;
}
else
{
v___y_389_ = v___y_402_;
v___y_390_ = v___y_405_;
v___y_391_ = v___y_406_;
v___y_392_ = v___y_407_;
v___y_393_ = v___y_403_;
v___y_394_ = v___y_404_;
v___y_395_ = v___x_400_;
goto v___jp_388_;
}
}
v___jp_409_:
{
if (v___y_410_ == 0)
{
lean_object* v_toCold_411_; lean_object* v_ref_412_; uint8_t v_suppressElabErrors_413_; lean_object* v_fileName_414_; lean_object* v_fileMap_415_; lean_object* v_options_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___f_419_; uint8_t v___x_420_; uint8_t v___x_421_; 
v_toCold_411_ = lean_ctor_get(v___y_312_, 0);
v_ref_412_ = lean_ctor_get(v___y_312_, 2);
v_suppressElabErrors_413_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*3 + 1);
v_fileName_414_ = lean_ctor_get(v_toCold_411_, 0);
v_fileMap_415_ = lean_ctor_get(v_toCold_411_, 1);
v_options_416_ = lean_ctor_get(v_toCold_411_, 2);
v___x_417_ = lean_box(v_suppressElabErrors_413_);
v___x_418_ = lean_box(v___y_410_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_419_, 0, v___x_417_);
lean_closure_set(v___f_419_, 1, v___x_418_);
v___x_420_ = 1;
v___x_421_ = l_Lean_instBEqMessageSeverity_beq(v_severity_308_, v___x_420_);
if (v___x_421_ == 0)
{
v___y_402_ = v___f_419_;
v___y_403_ = v_fileMap_415_;
v___y_404_ = v_fileName_414_;
v___y_405_ = v_suppressElabErrors_413_;
v___y_406_ = v___y_410_;
v___y_407_ = v_ref_412_;
v___y_408_ = v___x_421_;
goto v___jp_401_;
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_warningAsError;
v___x_423_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_416_, v___x_422_);
v___y_402_ = v___f_419_;
v___y_403_ = v_fileMap_415_;
v___y_404_ = v_fileName_414_;
v___y_405_ = v_suppressElabErrors_413_;
v___y_406_ = v___y_410_;
v___y_407_ = v_ref_412_;
v___y_408_ = v___x_423_;
goto v___jp_401_;
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_msgData_307_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_428_, lean_object* v_msgData_429_, lean_object* v_severity_430_, lean_object* v_isSilent_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v_severity_boxed_437_; uint8_t v_isSilent_boxed_438_; lean_object* v_res_439_; 
v_severity_boxed_437_ = lean_unbox(v_severity_430_);
v_isSilent_boxed_438_ = lean_unbox(v_isSilent_431_);
v_res_439_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_428_, v_msgData_429_, v_severity_boxed_437_, v_isSilent_boxed_438_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v_ref_428_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_440_, uint8_t v_severity_441_, uint8_t v_isSilent_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_ref_448_; lean_object* v___x_449_; 
v_ref_448_ = lean_ctor_get(v___y_445_, 2);
v___x_449_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_448_, v_msgData_440_, v_severity_441_, v_isSilent_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_450_, lean_object* v_severity_451_, lean_object* v_isSilent_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_severity_boxed_458_; uint8_t v_isSilent_boxed_459_; lean_object* v_res_460_; 
v_severity_boxed_458_ = lean_unbox(v_severity_451_);
v_isSilent_boxed_459_ = lean_unbox(v_isSilent_452_);
v_res_460_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_450_, v_severity_boxed_458_, v_isSilent_boxed_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = 1;
v___x_468_ = 0;
v___x_469_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_461_, v___x_467_, v___x_468_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_toCold_480_; lean_object* v_options_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_toCold_480_ = lean_ctor_get(v___y_478_, 0);
v_options_481_ = lean_ctor_get(v_toCold_480_, 2);
v___x_482_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_481_, v_opt_477_);
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_485_, v___y_486_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_opt_485_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v_env_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_524_; 
v___x_501_ = lean_st_ref_get(v___y_499_);
v_env_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_ref(v_env_502_);
lean_dec(v___x_501_);
v___x_503_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_504_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_503_, v___y_498_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_524_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_524_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_524_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v_isExporting_514_; 
v_isExporting_514_ = lean_ctor_get_uint8(v_env_502_, sizeof(void*)*8);
lean_dec_ref(v_env_502_);
if (v_isExporting_514_ == 0)
{
lean_dec(v_a_505_);
lean_dec(v_id_495_);
goto v___jp_509_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_isPrivateName(v_id_495_);
if (v___x_515_ == 0)
{
lean_dec(v_a_505_);
lean_dec(v_id_495_);
goto v___jp_509_;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
if (v___x_516_ == 0)
{
lean_dec(v_id_495_);
goto v___jp_509_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_del_object(v___x_507_);
v___x_517_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_518_ = 0;
v___x_519_ = l_Lean_MessageData_ofConstName(v_id_495_, v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_522_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_523_;
}
}
}
v___jp_509_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_box(0);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_510_);
v___x_512_ = v___x_507_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v___x_533_; 
v___x_533_ = lean_box(0);
return v___x_533_;
}
else
{
lean_object* v_head_534_; lean_object* v_tail_535_; lean_object* v_fst_536_; uint8_t v___x_537_; 
v_head_534_ = lean_ctor_get(v_x_532_, 0);
v_tail_535_ = lean_ctor_get(v_x_532_, 1);
v_fst_536_ = lean_ctor_get(v_head_534_, 0);
v___x_537_ = l_Lean_isPrivateName(v_fst_536_);
if (v___x_537_ == 0)
{
v_x_532_ = v_tail_535_;
goto _start;
}
else
{
lean_object* v___x_539_; 
lean_inc(v_head_534_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_head_534_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_540_);
lean_dec(v_x_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_542_, uint8_t v_enableLog_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_toCold_550_; lean_object* v_env_551_; lean_object* v_options_552_; lean_object* v_currNamespace_553_; lean_object* v_openDecls_554_; lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_res_557_; 
v___x_549_ = lean_st_ref_get(v___y_547_);
v_toCold_550_ = lean_ctor_get(v___y_546_, 0);
v_env_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_549_);
v_options_552_ = lean_ctor_get(v_toCold_550_, 2);
v_currNamespace_553_ = lean_ctor_get(v_toCold_550_, 4);
v_openDecls_554_ = lean_ctor_get(v_toCold_550_, 5);
v___x_555_ = lean_st_ref_get(v___y_547_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_ref(v_env_556_);
lean_dec(v___x_555_);
lean_inc(v_openDecls_554_);
lean_inc(v_currNamespace_553_);
v_res_557_ = l_Lean_ResolveName_resolveGlobalName(v_env_551_, v_options_552_, v_currNamespace_553_, v_openDecls_554_, v_id_542_);
if (v_enableLog_543_ == 0)
{
lean_object* v___x_558_; 
lean_dec_ref(v_env_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_res_557_);
return v___x_558_;
}
else
{
uint8_t v_isExporting_559_; 
v_isExporting_559_ = lean_ctor_get_uint8(v_env_556_, sizeof(void*)*8);
lean_dec_ref(v_env_556_);
if (v_isExporting_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_res_557_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_557_);
if (lean_obj_tag(v___x_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_fst_563_; lean_object* v___x_564_; 
v_val_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_561_, 1);
v_fst_563_ = lean_ctor_get(v_val_562_, 0);
lean_inc(v_fst_563_);
lean_dec(v_val_562_);
v___x_564_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_563_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_572_);
v___x_566_ = v___x_564_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_dec(v___x_564_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_res_557_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_res_557_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_res_557_);
v_a_573_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v___x_581_; 
lean_dec(v___x_561_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_res_557_);
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_582_, lean_object* v_enableLog_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v_enableLog_boxed_589_; lean_object* v_res_590_; 
v_enableLog_boxed_589_ = lean_unbox(v_enableLog_583_);
v_res_590_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_582_, v_enableLog_boxed_589_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_591_, lean_object* v_findLocalDecl_x3f_592_, lean_object* v_n_593_, lean_object* v_projs_594_, uint8_t v_globalDeclFound_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v_globalDeclFoundNext_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_imported_611_; lean_object* v_ctx_612_; lean_object* v_scopes_613_; lean_object* v_givenNameView_614_; uint8_t v___y_616_; 
v_imported_611_ = lean_ctor_get(v_view_591_, 1);
v_ctx_612_ = lean_ctor_get(v_view_591_, 2);
v_scopes_613_ = lean_ctor_get(v_view_591_, 3);
lean_inc(v_scopes_613_);
lean_inc(v_ctx_612_);
lean_inc(v_imported_611_);
lean_inc(v_n_593_);
v_givenNameView_614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_614_, 0, v_n_593_);
lean_ctor_set(v_givenNameView_614_, 1, v_imported_611_);
lean_ctor_set(v_givenNameView_614_, 2, v_ctx_612_);
lean_ctor_set(v_givenNameView_614_, 3, v_scopes_613_);
if (v_globalDeclFound_595_ == 0)
{
v___y_616_ = v_globalDeclFound_595_;
goto v___jp_615_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = l_List_isEmpty___redArg(v_projs_594_);
if (v___x_651_ == 0)
{
v___y_616_ = v_globalDeclFound_595_;
goto v___jp_615_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
v___y_616_ = v___x_652_;
goto v___jp_615_;
}
}
v___jp_601_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___y_603_);
lean_ctor_set(v___x_609_, 1, v_projs_594_);
v_n_593_ = v___y_602_;
v_projs_594_ = v___x_609_;
v_globalDeclFound_595_ = v_globalDeclFoundNext_604_;
v___y_596_ = v___y_605_;
v___y_597_ = v___y_606_;
v___y_598_ = v___y_607_;
v___y_599_ = v___y_608_;
goto _start;
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(v___y_616_);
lean_inc_ref(v_findLocalDecl_x3f_592_);
lean_inc_ref(v_givenNameView_614_);
v___x_618_ = lean_apply_2(v_findLocalDecl_x3f_592_, v_givenNameView_614_, v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
if (lean_obj_tag(v_n_593_) == 1)
{
if (v_globalDeclFound_595_ == 0)
{
lean_object* v_pre_619_; lean_object* v_str_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_pre_619_ = lean_ctor_get(v_n_593_, 0);
lean_inc(v_pre_619_);
v_str_620_ = lean_ctor_get(v_n_593_, 1);
lean_inc_ref(v_str_620_);
lean_dec_ref_known(v_n_593_, 2);
v___x_621_ = l_Lean_MacroScopesView_review(v_givenNameView_614_);
v___x_622_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_621_, v_globalDeclFound_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v_r_625_; uint8_t v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_box(0);
v_r_625_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_623_, v___x_624_);
v___x_626_ = l_List_isEmpty___redArg(v_r_625_);
lean_dec(v_r_625_);
if (v___x_626_ == 0)
{
uint8_t v_globalDeclFoundNext_627_; 
v_globalDeclFoundNext_627_ = 1;
v___y_602_ = v_pre_619_;
v___y_603_ = v_str_620_;
v_globalDeclFoundNext_604_ = v_globalDeclFoundNext_627_;
v___y_605_ = v___y_596_;
v___y_606_ = v___y_597_;
v___y_607_ = v___y_598_;
v___y_608_ = v___y_599_;
goto v___jp_601_;
}
else
{
v___y_602_ = v_pre_619_;
v___y_603_ = v_str_620_;
v_globalDeclFoundNext_604_ = v_globalDeclFound_595_;
v___y_605_ = v___y_596_;
v___y_606_ = v___y_597_;
v___y_607_ = v___y_598_;
v___y_608_ = v___y_599_;
goto v___jp_601_;
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_str_620_);
lean_dec(v_pre_619_);
lean_dec(v_projs_594_);
lean_dec_ref(v_findLocalDecl_x3f_592_);
v_a_628_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_622_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_622_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_pre_636_; lean_object* v_str_637_; 
lean_dec_ref_known(v_givenNameView_614_, 4);
v_pre_636_ = lean_ctor_get(v_n_593_, 0);
lean_inc(v_pre_636_);
v_str_637_ = lean_ctor_get(v_n_593_, 1);
lean_inc_ref(v_str_637_);
lean_dec_ref_known(v_n_593_, 2);
v___y_602_ = v_pre_636_;
v___y_603_ = v_str_637_;
v_globalDeclFoundNext_604_ = v_globalDeclFound_595_;
v___y_605_ = v___y_596_;
v___y_606_ = v___y_597_;
v___y_607_ = v___y_598_;
v___y_608_ = v___y_599_;
goto v___jp_601_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref_known(v_givenNameView_614_, 4);
lean_dec(v_projs_594_);
lean_dec(v_n_593_);
lean_dec_ref(v_findLocalDecl_x3f_592_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
else
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref_known(v_givenNameView_614_, 4);
lean_dec(v_n_593_);
lean_dec_ref(v_findLocalDecl_x3f_592_);
v_val_640_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_650_ == 0)
{
v___x_642_ = v___x_618_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v___x_618_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = l_Lean_LocalDecl_toExpr(v_val_640_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_projs_594_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_653_, lean_object* v_findLocalDecl_x3f_654_, lean_object* v_n_655_, lean_object* v_projs_656_, lean_object* v_globalDeclFound_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v_globalDeclFound_boxed_663_; lean_object* v_res_664_; 
v_globalDeclFound_boxed_663_ = lean_unbox(v_globalDeclFound_657_);
v_res_664_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_653_, v_findLocalDecl_x3f_654_, v_n_655_, v_projs_656_, v_globalDeclFound_boxed_663_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_view_653_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_665_, lean_object* v_k_666_){
_start:
{
if (lean_obj_tag(v_t_665_) == 0)
{
lean_object* v_k_667_; lean_object* v_v_668_; lean_object* v_l_669_; lean_object* v_r_670_; uint8_t v___x_671_; 
v_k_667_ = lean_ctor_get(v_t_665_, 1);
v_v_668_ = lean_ctor_get(v_t_665_, 2);
v_l_669_ = lean_ctor_get(v_t_665_, 3);
v_r_670_ = lean_ctor_get(v_t_665_, 4);
v___x_671_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_666_, v_k_667_);
switch(v___x_671_)
{
case 0:
{
v_t_665_ = v_l_669_;
goto _start;
}
case 1:
{
lean_object* v___x_673_; 
lean_inc(v_v_668_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v_v_668_);
return v___x_673_;
}
default: 
{
v_t_665_ = v_r_670_;
goto _start;
}
}
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_676_, lean_object* v_k_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_676_, v_k_677_);
lean_dec(v_k_677_);
lean_dec(v_t_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_679_, lean_object* v_givenName_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = l_Lean_LocalDecl_userName(v_localDecl_679_);
v___x_682_ = lean_name_eq(v___x_681_, v_givenName_680_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec_ref(v_localDecl_679_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_localDecl_679_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_685_, lean_object* v_givenName_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_685_, v_givenName_686_);
lean_dec(v_givenName_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_688_, uint8_t v_skipAuxDecl_689_, lean_object* v_auxDeclToFullName_690_, lean_object* v___x_691_, lean_object* v_givenNameView_692_, lean_object* v_as_693_, lean_object* v_i_694_){
_start:
{
lean_object* v_zero_695_; uint8_t v_isZero_696_; 
v_zero_695_ = lean_unsigned_to_nat(0u);
v_isZero_696_ = lean_nat_dec_eq(v_i_694_, v_zero_695_);
if (v_isZero_696_ == 1)
{
lean_object* v___x_697_; 
lean_dec(v_i_694_);
lean_dec_ref(v_givenNameView_692_);
lean_dec(v___x_691_);
v___x_697_ = lean_box(0);
return v___x_697_;
}
else
{
lean_object* v_one_698_; lean_object* v_n_699_; lean_object* v___y_701_; lean_object* v___x_703_; 
v_one_698_ = lean_unsigned_to_nat(1u);
v_n_699_ = lean_nat_sub(v_i_694_, v_one_698_);
lean_dec(v_i_694_);
v___x_703_ = lean_array_fget_borrowed(v_as_693_, v_n_699_);
if (lean_obj_tag(v___x_703_) == 0)
{
v___y_701_ = v___x_703_;
goto v___jp_700_;
}
else
{
lean_object* v_val_704_; uint8_t v___x_705_; 
v_val_704_ = lean_ctor_get(v___x_703_, 0);
v___x_705_ = l_Lean_LocalDecl_isAuxDecl(v_val_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_inc(v_val_704_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_704_, v_givenName_688_);
v___y_701_ = v___x_706_;
goto v___jp_700_;
}
else
{
if (v_skipAuxDecl_689_ == 0)
{
if (v___x_705_ == 0)
{
v_i_694_ = v_n_699_;
goto _start;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Lean_LocalDecl_fvarId(v_val_704_);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_690_, v___x_708_);
lean_dec(v___x_708_);
if (lean_obj_tag(v___x_709_) == 1)
{
lean_object* v_val_710_; lean_object* v_fullDeclView_711_; lean_object* v___y_713_; lean_object* v_name_734_; lean_object* v___x_735_; 
v_val_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v___x_709_, 1);
v_fullDeclView_711_ = l_Lean_extractMacroScopes(v_val_710_);
v_name_734_ = lean_ctor_get(v_fullDeclView_711_, 0);
lean_inc_n(v_name_734_, 2);
v___x_735_ = l_Lean_privateToUserName_x3f(v_name_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
v___y_713_ = v_name_734_;
goto v___jp_712_;
}
else
{
lean_object* v_val_736_; 
lean_dec(v_name_734_);
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v___y_713_ = v_val_736_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v_imported_714_; lean_object* v_ctx_715_; lean_object* v_scopes_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_732_; 
v_imported_714_ = lean_ctor_get(v_fullDeclView_711_, 1);
v_ctx_715_ = lean_ctor_get(v_fullDeclView_711_, 2);
v_scopes_716_ = lean_ctor_get(v_fullDeclView_711_, 3);
v_isSharedCheck_732_ = !lean_is_exclusive(v_fullDeclView_711_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_fullDeclView_711_, 0);
lean_dec(v_unused_733_);
v___x_718_ = v_fullDeclView_711_;
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_scopes_716_);
lean_inc(v_ctx_715_);
lean_inc(v_imported_714_);
lean_dec(v_fullDeclView_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fullDeclView_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___y_713_);
v_fullDeclView_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___y_713_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_imported_714_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_ctx_715_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_scopes_716_);
v_fullDeclView_721_ = v_reuseFailAlloc_731_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v_fullDeclName_722_; uint8_t v___x_723_; 
lean_inc_ref(v_fullDeclView_721_);
v_fullDeclName_722_ = l_Lean_MacroScopesView_review(v_fullDeclView_721_);
v___x_723_ = l_Lean_Name_isPrefixOf(v___x_691_, v_fullDeclName_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec_ref(v_fullDeclView_721_);
lean_inc(v___x_691_);
lean_inc_ref(v_givenNameView_692_);
lean_inc(v_val_704_);
v___x_724_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_704_, v_givenNameView_692_, v_fullDeclName_722_, v___x_691_);
lean_dec(v_fullDeclName_722_);
v___y_701_ = v___x_724_;
goto v___jp_700_;
}
else
{
lean_object* v___x_725_; lean_object* v_localDeclNameView_726_; uint8_t v___x_727_; 
lean_dec(v_fullDeclName_722_);
v___x_725_ = l_Lean_LocalDecl_userName(v_val_704_);
v_localDeclNameView_726_ = l_Lean_extractMacroScopes(v___x_725_);
v___x_727_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_726_, v_givenNameView_692_);
lean_dec_ref(v_localDeclNameView_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v_fullDeclView_721_);
v_i_694_ = v_n_699_;
goto _start;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_692_, v_fullDeclView_721_);
lean_dec_ref(v_fullDeclView_721_);
if (v___x_729_ == 0)
{
v_i_694_ = v_n_699_;
goto _start;
}
else
{
lean_inc_ref(v___x_703_);
v___y_701_ = v___x_703_;
goto v___jp_700_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v___x_709_);
lean_inc(v_val_704_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_704_, v_givenName_688_);
v___y_701_ = v___x_737_;
goto v___jp_700_;
}
}
}
else
{
v_i_694_ = v_n_699_;
goto _start;
}
}
}
v___jp_700_:
{
if (lean_obj_tag(v___y_701_) == 0)
{
v_i_694_ = v_n_699_;
goto _start;
}
else
{
lean_dec(v_n_699_);
lean_dec_ref(v_givenNameView_692_);
lean_dec(v___x_691_);
return v___y_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_739_, lean_object* v_skipAuxDecl_740_, lean_object* v_auxDeclToFullName_741_, lean_object* v___x_742_, lean_object* v_givenNameView_743_, lean_object* v_as_744_, lean_object* v_i_745_){
_start:
{
uint8_t v_skipAuxDecl_boxed_746_; lean_object* v_res_747_; 
v_skipAuxDecl_boxed_746_ = lean_unbox(v_skipAuxDecl_740_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_739_, v_skipAuxDecl_boxed_746_, v_auxDeclToFullName_741_, v___x_742_, v_givenNameView_743_, v_as_744_, v_i_745_);
lean_dec_ref(v_as_744_);
lean_dec(v_auxDeclToFullName_741_);
lean_dec(v_givenName_739_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_748_, uint8_t v_skipAuxDecl_749_, lean_object* v_auxDeclToFullName_750_, lean_object* v___x_751_, lean_object* v_givenNameView_752_, lean_object* v_as_753_, lean_object* v_i_754_){
_start:
{
lean_object* v_zero_755_; uint8_t v_isZero_756_; 
v_zero_755_ = lean_unsigned_to_nat(0u);
v_isZero_756_ = lean_nat_dec_eq(v_i_754_, v_zero_755_);
if (v_isZero_756_ == 1)
{
lean_object* v___x_757_; 
lean_dec(v_i_754_);
lean_dec_ref(v_givenNameView_752_);
lean_dec(v___x_751_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
else
{
lean_object* v_one_758_; lean_object* v_n_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_one_758_ = lean_unsigned_to_nat(1u);
v_n_759_ = lean_nat_sub(v_i_754_, v_one_758_);
lean_dec(v_i_754_);
v___x_760_ = lean_array_fget_borrowed(v_as_753_, v_n_759_);
lean_inc_ref(v_givenNameView_752_);
lean_inc(v___x_751_);
v___x_761_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_748_, v_skipAuxDecl_749_, v_auxDeclToFullName_750_, v___x_751_, v_givenNameView_752_, v___x_760_);
if (lean_obj_tag(v___x_761_) == 0)
{
v_i_754_ = v_n_759_;
goto _start;
}
else
{
lean_dec(v_n_759_);
lean_dec_ref(v_givenNameView_752_);
lean_dec(v___x_751_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_763_, uint8_t v_skipAuxDecl_764_, lean_object* v_auxDeclToFullName_765_, lean_object* v___x_766_, lean_object* v_givenNameView_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v_cs_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_cs_769_ = lean_ctor_get(v_x_768_, 0);
v___x_770_ = lean_array_get_size(v_cs_769_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_763_, v_skipAuxDecl_764_, v_auxDeclToFullName_765_, v___x_766_, v_givenNameView_767_, v_cs_769_, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_vs_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_vs_772_ = lean_ctor_get(v_x_768_, 0);
v___x_773_ = lean_array_get_size(v_vs_772_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_763_, v_skipAuxDecl_764_, v_auxDeclToFullName_765_, v___x_766_, v_givenNameView_767_, v_vs_772_, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_775_, lean_object* v_skipAuxDecl_776_, lean_object* v_auxDeclToFullName_777_, lean_object* v___x_778_, lean_object* v_givenNameView_779_, lean_object* v_x_780_){
_start:
{
uint8_t v_skipAuxDecl_boxed_781_; lean_object* v_res_782_; 
v_skipAuxDecl_boxed_781_ = lean_unbox(v_skipAuxDecl_776_);
v_res_782_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_775_, v_skipAuxDecl_boxed_781_, v_auxDeclToFullName_777_, v___x_778_, v_givenNameView_779_, v_x_780_);
lean_dec_ref(v_x_780_);
lean_dec(v_auxDeclToFullName_777_);
lean_dec(v_givenName_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_783_, lean_object* v_skipAuxDecl_784_, lean_object* v_auxDeclToFullName_785_, lean_object* v___x_786_, lean_object* v_givenNameView_787_, lean_object* v_as_788_, lean_object* v_i_789_){
_start:
{
uint8_t v_skipAuxDecl_boxed_790_; lean_object* v_res_791_; 
v_skipAuxDecl_boxed_790_ = lean_unbox(v_skipAuxDecl_784_);
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_783_, v_skipAuxDecl_boxed_790_, v_auxDeclToFullName_785_, v___x_786_, v_givenNameView_787_, v_as_788_, v_i_789_);
lean_dec_ref(v_as_788_);
lean_dec(v_auxDeclToFullName_785_);
lean_dec(v_givenName_783_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_792_, uint8_t v_skipAuxDecl_793_, lean_object* v_auxDeclToFullName_794_, lean_object* v___x_795_, lean_object* v_givenNameView_796_, lean_object* v_t_797_){
_start:
{
lean_object* v_root_798_; lean_object* v_tail_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_root_798_ = lean_ctor_get(v_t_797_, 0);
v_tail_799_ = lean_ctor_get(v_t_797_, 1);
v___x_800_ = lean_array_get_size(v_tail_799_);
lean_inc_ref(v_givenNameView_796_);
lean_inc(v___x_795_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_792_, v_skipAuxDecl_793_, v_auxDeclToFullName_794_, v___x_795_, v_givenNameView_796_, v_tail_799_, v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_792_, v_skipAuxDecl_793_, v_auxDeclToFullName_794_, v___x_795_, v_givenNameView_796_, v_root_798_);
return v___x_802_;
}
else
{
lean_dec_ref(v_givenNameView_796_);
lean_dec(v___x_795_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_803_, lean_object* v_skipAuxDecl_804_, lean_object* v_auxDeclToFullName_805_, lean_object* v___x_806_, lean_object* v_givenNameView_807_, lean_object* v_t_808_){
_start:
{
uint8_t v_skipAuxDecl_boxed_809_; lean_object* v_res_810_; 
v_skipAuxDecl_boxed_809_ = lean_unbox(v_skipAuxDecl_804_);
v_res_810_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_803_, v_skipAuxDecl_boxed_809_, v_auxDeclToFullName_805_, v___x_806_, v_givenNameView_807_, v_t_808_);
lean_dec_ref(v_t_808_);
lean_dec(v_auxDeclToFullName_805_);
lean_dec(v_givenName_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_811_, lean_object* v_givenName_812_, lean_object* v_as_813_, lean_object* v_i_814_){
_start:
{
lean_object* v_zero_815_; uint8_t v_isZero_816_; 
v_zero_815_ = lean_unsigned_to_nat(0u);
v_isZero_816_ = lean_nat_dec_eq(v_i_814_, v_zero_815_);
if (v_isZero_816_ == 1)
{
lean_object* v___x_817_; 
lean_dec(v_i_814_);
v___x_817_ = lean_box(0);
return v___x_817_;
}
else
{
lean_object* v_one_818_; lean_object* v_n_819_; lean_object* v___y_821_; lean_object* v___x_823_; 
v_one_818_ = lean_unsigned_to_nat(1u);
v_n_819_ = lean_nat_sub(v_i_814_, v_one_818_);
lean_dec(v_i_814_);
v___x_823_ = lean_array_fget_borrowed(v_as_813_, v_n_819_);
if (lean_obj_tag(v___x_823_) == 0)
{
v___y_821_ = v___x_823_;
goto v___jp_820_;
}
else
{
lean_object* v_val_824_; uint8_t v___x_825_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
v___x_825_ = l_Lean_LocalDecl_isAuxDecl(v_val_824_);
if (v___x_825_ == 0)
{
v___y_821_ = v_localDecl_x3f_811_;
goto v___jp_820_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = l_Lean_LocalDecl_userName(v_val_824_);
v___x_827_ = lean_name_eq(v___x_826_, v_givenName_812_);
lean_dec(v___x_826_);
if (v___x_827_ == 0)
{
v_i_814_ = v_n_819_;
goto _start;
}
else
{
v___y_821_ = v___x_823_;
goto v___jp_820_;
}
}
}
v___jp_820_:
{
if (lean_obj_tag(v___y_821_) == 0)
{
v_i_814_ = v_n_819_;
goto _start;
}
else
{
lean_dec(v_n_819_);
lean_inc_ref(v___y_821_);
return v___y_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_829_, lean_object* v_givenName_830_, lean_object* v_as_831_, lean_object* v_i_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_829_, v_givenName_830_, v_as_831_, v_i_832_);
lean_dec_ref(v_as_831_);
lean_dec(v_givenName_830_);
lean_dec(v_localDecl_x3f_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_834_, lean_object* v_givenName_835_, lean_object* v_as_836_, lean_object* v_i_837_){
_start:
{
lean_object* v_zero_838_; uint8_t v_isZero_839_; 
v_zero_838_ = lean_unsigned_to_nat(0u);
v_isZero_839_ = lean_nat_dec_eq(v_i_837_, v_zero_838_);
if (v_isZero_839_ == 1)
{
lean_object* v___x_840_; 
lean_dec(v_i_837_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
else
{
lean_object* v_one_841_; lean_object* v_n_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_one_841_ = lean_unsigned_to_nat(1u);
v_n_842_ = lean_nat_sub(v_i_837_, v_one_841_);
lean_dec(v_i_837_);
v___x_843_ = lean_array_fget_borrowed(v_as_836_, v_n_842_);
v___x_844_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_834_, v_givenName_835_, v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
v_i_837_ = v_n_842_;
goto _start;
}
else
{
lean_dec(v_n_842_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_846_, lean_object* v_givenName_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_cs_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_cs_849_ = lean_ctor_get(v_x_848_, 0);
v___x_850_ = lean_array_get_size(v_cs_849_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_846_, v_givenName_847_, v_cs_849_, v___x_850_);
return v___x_851_;
}
else
{
lean_object* v_vs_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_vs_852_ = lean_ctor_get(v_x_848_, 0);
v___x_853_ = lean_array_get_size(v_vs_852_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_846_, v_givenName_847_, v_vs_852_, v___x_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_855_, lean_object* v_givenName_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_855_, v_givenName_856_, v_x_857_);
lean_dec_ref(v_x_857_);
lean_dec(v_givenName_856_);
lean_dec(v_localDecl_x3f_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_859_, lean_object* v_givenName_860_, lean_object* v_as_861_, lean_object* v_i_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_859_, v_givenName_860_, v_as_861_, v_i_862_);
lean_dec_ref(v_as_861_);
lean_dec(v_givenName_860_);
lean_dec(v_localDecl_x3f_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_864_, lean_object* v_givenName_865_, lean_object* v_t_866_){
_start:
{
lean_object* v_root_867_; lean_object* v_tail_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_root_867_ = lean_ctor_get(v_t_866_, 0);
v_tail_868_ = lean_ctor_get(v_t_866_, 1);
v___x_869_ = lean_array_get_size(v_tail_868_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_864_, v_givenName_865_, v_tail_868_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_864_, v_givenName_865_, v_root_867_);
return v___x_871_;
}
else
{
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_872_, lean_object* v_givenName_873_, lean_object* v_t_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_872_, v_givenName_873_, v_t_874_);
lean_dec_ref(v_t_874_);
lean_dec(v_givenName_873_);
lean_dec(v_localDecl_x3f_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_876_, lean_object* v_currNamespace_877_, lean_object* v_decls_878_, lean_object* v_givenNameView_879_, uint8_t v_skipAuxDecl_880_){
_start:
{
lean_object* v_givenName_881_; lean_object* v_localDecl_x3f_882_; 
lean_inc_ref(v_givenNameView_879_);
v_givenName_881_ = l_Lean_MacroScopesView_review(v_givenNameView_879_);
v_localDecl_x3f_882_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_881_, v_skipAuxDecl_880_, v_auxDeclToFullName_876_, v_currNamespace_877_, v_givenNameView_879_, v_decls_878_);
if (lean_obj_tag(v_localDecl_x3f_882_) == 0)
{
if (v_skipAuxDecl_880_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_882_, v_givenName_881_, v_decls_878_);
lean_dec(v_givenName_881_);
return v___x_883_;
}
else
{
lean_dec(v_givenName_881_);
return v_localDecl_x3f_882_;
}
}
else
{
lean_dec(v_givenName_881_);
return v_localDecl_x3f_882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_884_, lean_object* v_currNamespace_885_, lean_object* v_decls_886_, lean_object* v_givenNameView_887_, lean_object* v_skipAuxDecl_888_){
_start:
{
uint8_t v_skipAuxDecl_boxed_889_; lean_object* v_res_890_; 
v_skipAuxDecl_boxed_889_ = lean_unbox(v_skipAuxDecl_888_);
v_res_890_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_884_, v_currNamespace_885_, v_decls_886_, v_givenNameView_887_, v_skipAuxDecl_boxed_889_);
lean_dec_ref(v_decls_886_);
lean_dec(v_auxDeclToFullName_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_lctx_897_; lean_object* v_toCold_898_; lean_object* v_decls_899_; lean_object* v_auxDeclToFullName_900_; lean_object* v_currNamespace_901_; lean_object* v_view_902_; lean_object* v_name_903_; lean_object* v_findLocalDecl_x3f_904_; lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
v_lctx_897_ = lean_ctor_get(v___y_892_, 2);
v_toCold_898_ = lean_ctor_get(v___y_894_, 0);
v_decls_899_ = lean_ctor_get(v_lctx_897_, 1);
v_auxDeclToFullName_900_ = lean_ctor_get(v_lctx_897_, 2);
v_currNamespace_901_ = lean_ctor_get(v_toCold_898_, 4);
v_view_902_ = l_Lean_extractMacroScopes(v_n_891_);
v_name_903_ = lean_ctor_get(v_view_902_, 0);
lean_inc(v_name_903_);
lean_inc_ref(v_decls_899_);
lean_inc(v_currNamespace_901_);
lean_inc(v_auxDeclToFullName_900_);
v_findLocalDecl_x3f_904_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_904_, 0, v_auxDeclToFullName_900_);
lean_closure_set(v_findLocalDecl_x3f_904_, 1, v_currNamespace_901_);
lean_closure_set(v_findLocalDecl_x3f_904_, 2, v_decls_899_);
v___x_905_ = lean_box(0);
v___x_906_ = 0;
v___x_907_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_902_, v_findLocalDecl_x3f_904_, v_name_903_, v___x_905_, v___x_906_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec_ref(v_view_902_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_915_, lean_object* v_n_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_936_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_936_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 0)
{
uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = 1;
v___x_928_ = lean_box(v___x_927_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec_ref_known(v_a_923_, 1);
v___x_932_ = lean_box(v___x_915_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_932_);
v___x_934_ = v___x_925_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
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
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_922_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_922_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_945_, lean_object* v_n_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
uint8_t v___x_43925__boxed_952_; lean_object* v_res_953_; 
v___x_43925__boxed_952_ = lean_unbox(v___x_945_);
v_res_953_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(v___x_43925__boxed_952_, v_n_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_954_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_toCold_971_; lean_object* v_options_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_toCold_971_ = lean_ctor_get(v___y_969_, 0);
v_options_972_ = lean_ctor_get(v_toCold_971_, 2);
v___x_973_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_972_, v_opt_968_);
v___x_974_ = lean_box(v___x_973_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_977_, v___y_978_);
lean_dec_ref(v___y_978_);
lean_dec_ref(v_opt_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_983_, lean_object* v_msgData_984_, uint8_t v_severity_985_, uint8_t v_isSilent_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_a_993_; lean_object* v___y_997_; uint8_t v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___y_1037_; uint8_t v___y_1038_; uint8_t v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1060_; uint8_t v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; uint8_t v___y_1071_; uint8_t v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; uint8_t v___x_1079_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; uint8_t v___y_1089_; uint8_t v___x_1105_; 
v___x_1079_ = 2;
v___x_1105_ = l_Lean_instBEqMessageSeverity_beq(v_severity_985_, v___x_1079_);
if (v___x_1105_ == 0)
{
v___y_1089_ = v___x_1105_;
goto v___jp_1088_;
}
else
{
uint8_t v___x_1106_; 
lean_inc_ref(v_msgData_984_);
v___x_1106_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_984_);
v___y_1089_ = v___x_1106_;
goto v___jp_1088_;
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_a_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
v___jp_996_:
{
lean_object* v___x_1006_; lean_object* v_toCold_1007_; lean_object* v_currNamespace_1008_; lean_object* v_openDecls_1009_; lean_object* v_env_1010_; lean_object* v_nextMacroScope_1011_; lean_object* v_ngen_1012_; lean_object* v_auxDeclNGen_1013_; lean_object* v_traceState_1014_; lean_object* v_cache_1015_; lean_object* v_messages_1016_; lean_object* v_infoState_1017_; lean_object* v_snapshotTasks_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1031_; 
v___x_1006_ = lean_st_ref_take(v___y_1005_);
v_toCold_1007_ = lean_ctor_get(v___y_1004_, 0);
v_currNamespace_1008_ = lean_ctor_get(v_toCold_1007_, 4);
v_openDecls_1009_ = lean_ctor_get(v_toCold_1007_, 5);
v_env_1010_ = lean_ctor_get(v___x_1006_, 0);
v_nextMacroScope_1011_ = lean_ctor_get(v___x_1006_, 1);
v_ngen_1012_ = lean_ctor_get(v___x_1006_, 2);
v_auxDeclNGen_1013_ = lean_ctor_get(v___x_1006_, 3);
v_traceState_1014_ = lean_ctor_get(v___x_1006_, 4);
v_cache_1015_ = lean_ctor_get(v___x_1006_, 5);
v_messages_1016_ = lean_ctor_get(v___x_1006_, 6);
v_infoState_1017_ = lean_ctor_get(v___x_1006_, 7);
v_snapshotTasks_1018_ = lean_ctor_get(v___x_1006_, 8);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1020_ = v___x_1006_;
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snapshotTasks_1018_);
lean_inc(v_infoState_1017_);
lean_inc(v_messages_1016_);
lean_inc(v_cache_1015_);
lean_inc(v_traceState_1014_);
lean_inc(v_auxDeclNGen_1013_);
lean_inc(v_ngen_1012_);
lean_inc(v_nextMacroScope_1011_);
lean_inc(v_env_1010_);
lean_dec(v___x_1006_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_inc(v_openDecls_1009_);
lean_inc(v_currNamespace_1008_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_currNamespace_1008_);
lean_ctor_set(v___x_1022_, 1, v_openDecls_1009_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___y_1000_);
lean_inc_ref(v___y_997_);
lean_inc_ref(v___y_999_);
v___x_1024_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1024_, 0, v___y_999_);
lean_ctor_set(v___x_1024_, 1, v___y_1002_);
lean_ctor_set(v___x_1024_, 2, v___y_1003_);
lean_ctor_set(v___x_1024_, 3, v___y_997_);
lean_ctor_set(v___x_1024_, 4, v___x_1023_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*5, v___y_1001_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*5 + 1, v___y_998_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*5 + 2, v_isSilent_986_);
v___x_1025_ = l_Lean_MessageLog_add(v___x_1024_, v_messages_1016_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 6, v___x_1025_);
v___x_1027_ = v___x_1020_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_env_1010_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_nextMacroScope_1011_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_ngen_1012_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_auxDeclNGen_1013_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_traceState_1014_);
lean_ctor_set(v_reuseFailAlloc_1030_, 5, v_cache_1015_);
lean_ctor_set(v_reuseFailAlloc_1030_, 6, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1030_, 7, v_infoState_1017_);
lean_ctor_set(v_reuseFailAlloc_1030_, 8, v_snapshotTasks_1018_);
v___x_1027_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_st_ref_put(v___y_1005_, v___x_1027_);
v___x_1029_ = lean_box(0);
v_a_993_ = v___x_1029_;
goto v___jp_992_;
}
}
}
v___jp_1032_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1055_; 
v___x_1041_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_984_);
v___x_1042_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1041_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_inc_ref_n(v___y_1034_, 2);
v___x_1047_ = l_Lean_FileMap_toPosition(v___y_1034_, v___y_1037_);
lean_dec(v___y_1037_);
v___x_1048_ = l_Lean_FileMap_toPosition(v___y_1034_, v___y_1040_);
lean_dec(v___y_1040_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1039_ == 0)
{
lean_dec_ref(v___y_1033_);
v___y_997_ = v___x_1051_;
v___y_998_ = v___y_1036_;
v___y_999_ = v___y_1035_;
v___y_1000_ = v_a_1043_;
v___y_1001_ = v___y_1038_;
v___y_1002_ = v___x_1047_;
v___y_1003_ = v___x_1050_;
v___y_1004_ = v___y_989_;
v___y_1005_ = v___y_990_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1052_; 
lean_inc(v_a_1043_);
v___x_1052_ = l_Lean_MessageData_hasTag(v___y_1033_, v_a_1043_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v___x_1047_);
lean_dec(v_a_1043_);
v___x_1053_ = lean_box(0);
v_a_993_ = v___x_1053_;
goto v___jp_992_;
}
else
{
v___y_997_ = v___x_1051_;
v___y_998_ = v___y_1036_;
v___y_999_ = v___y_1035_;
v___y_1000_ = v_a_1043_;
v___y_1001_ = v___y_1038_;
v___y_1002_ = v___x_1047_;
v___y_1003_ = v___x_1050_;
v___y_1004_ = v___y_989_;
v___y_1005_ = v___y_990_;
goto v___jp_996_;
}
}
}
}
}
v___jp_1056_:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Syntax_getTailPos_x3f(v___y_1062_, v___y_1061_);
lean_dec(v___y_1062_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_inc(v___y_1064_);
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1060_;
v___y_1036_ = v___y_1059_;
v___y_1037_ = v___y_1064_;
v___y_1038_ = v___y_1061_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v___y_1064_;
goto v___jp_1032_;
}
else
{
lean_object* v_val_1066_; 
v_val_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1060_;
v___y_1036_ = v___y_1059_;
v___y_1037_ = v___y_1064_;
v___y_1038_ = v___y_1061_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v_val_1066_;
goto v___jp_1032_;
}
}
v___jp_1067_:
{
lean_object* v_ref_1075_; lean_object* v___x_1076_; 
v_ref_1075_ = l_Lean_replaceRef(v_ref_983_, v___y_1073_);
v___x_1076_ = l_Lean_Syntax_getPos_x3f(v_ref_1075_, v___y_1071_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___y_1057_ = v___y_1068_;
v___y_1058_ = v___y_1069_;
v___y_1059_ = v___y_1074_;
v___y_1060_ = v___y_1070_;
v___y_1061_ = v___y_1071_;
v___y_1062_ = v_ref_1075_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v___x_1077_;
goto v___jp_1056_;
}
else
{
lean_object* v_val_1078_; 
v_val_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1076_, 1);
v___y_1057_ = v___y_1068_;
v___y_1058_ = v___y_1069_;
v___y_1059_ = v___y_1074_;
v___y_1060_ = v___y_1070_;
v___y_1061_ = v___y_1071_;
v___y_1062_ = v_ref_1075_;
v___y_1063_ = v___y_1072_;
v___y_1064_ = v_val_1078_;
goto v___jp_1056_;
}
}
v___jp_1080_:
{
if (v___y_1087_ == 0)
{
v___y_1068_ = v___y_1083_;
v___y_1069_ = v___y_1081_;
v___y_1070_ = v___y_1082_;
v___y_1071_ = v___y_1084_;
v___y_1072_ = v___y_1085_;
v___y_1073_ = v___y_1086_;
v___y_1074_ = v_severity_985_;
goto v___jp_1067_;
}
else
{
v___y_1068_ = v___y_1083_;
v___y_1069_ = v___y_1081_;
v___y_1070_ = v___y_1082_;
v___y_1071_ = v___y_1084_;
v___y_1072_ = v___y_1085_;
v___y_1073_ = v___y_1086_;
v___y_1074_ = v___x_1079_;
goto v___jp_1067_;
}
}
v___jp_1088_:
{
if (v___y_1089_ == 0)
{
lean_object* v_toCold_1090_; lean_object* v_ref_1091_; uint8_t v_suppressElabErrors_1092_; lean_object* v_fileName_1093_; lean_object* v_fileMap_1094_; lean_object* v_options_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___f_1098_; uint8_t v___x_1099_; uint8_t v___x_1100_; 
v_toCold_1090_ = lean_ctor_get(v___y_989_, 0);
v_ref_1091_ = lean_ctor_get(v___y_989_, 2);
v_suppressElabErrors_1092_ = lean_ctor_get_uint8(v___y_989_, sizeof(void*)*3 + 1);
v_fileName_1093_ = lean_ctor_get(v_toCold_1090_, 0);
v_fileMap_1094_ = lean_ctor_get(v_toCold_1090_, 1);
v_options_1095_ = lean_ctor_get(v_toCold_1090_, 2);
v___x_1096_ = lean_box(v_suppressElabErrors_1092_);
v___x_1097_ = lean_box(v___y_1089_);
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1098_, 0, v___x_1096_);
lean_closure_set(v___f_1098_, 1, v___x_1097_);
v___x_1099_ = 1;
v___x_1100_ = l_Lean_instBEqMessageSeverity_beq(v_severity_985_, v___x_1099_);
if (v___x_1100_ == 0)
{
v___y_1081_ = v_fileMap_1094_;
v___y_1082_ = v_fileName_1093_;
v___y_1083_ = v___f_1098_;
v___y_1084_ = v___y_1089_;
v___y_1085_ = v_suppressElabErrors_1092_;
v___y_1086_ = v_ref_1091_;
v___y_1087_ = v___x_1100_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = l_Lean_warningAsError;
v___x_1102_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_1095_, v___x_1101_);
v___y_1081_ = v_fileMap_1094_;
v___y_1082_ = v_fileName_1093_;
v___y_1083_ = v___f_1098_;
v___y_1084_ = v___y_1089_;
v___y_1085_ = v_suppressElabErrors_1092_;
v___y_1086_ = v_ref_1091_;
v___y_1087_ = v___x_1102_;
goto v___jp_1080_;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_msgData_984_);
v___x_1103_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_1107_, lean_object* v_msgData_1108_, lean_object* v_severity_1109_, lean_object* v_isSilent_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v_severity_boxed_1116_; uint8_t v_isSilent_boxed_1117_; lean_object* v_res_1118_; 
v_severity_boxed_1116_ = lean_unbox(v_severity_1109_);
v_isSilent_boxed_1117_ = lean_unbox(v_isSilent_1110_);
v_res_1118_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1107_, v_msgData_1108_, v_severity_boxed_1116_, v_isSilent_boxed_1117_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v_ref_1107_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_1119_, uint8_t v_severity_1120_, uint8_t v_isSilent_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_ref_1127_; lean_object* v___x_1128_; 
v_ref_1127_ = lean_ctor_get(v___y_1124_, 2);
v___x_1128_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1127_, v_msgData_1119_, v_severity_1120_, v_isSilent_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_1129_, lean_object* v_severity_1130_, lean_object* v_isSilent_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_severity_boxed_1137_; uint8_t v_isSilent_boxed_1138_; lean_object* v_res_1139_; 
v_severity_boxed_1137_ = lean_unbox(v_severity_1130_);
v_isSilent_boxed_1138_ = lean_unbox(v_isSilent_1131_);
v_res_1139_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1129_, v_severity_boxed_1137_, v_isSilent_boxed_1138_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
uint8_t v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = 1;
v___x_1147_ = 0;
v___x_1148_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1140_, v___x_1146_, v___x_1147_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_env_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1186_; 
v___x_1162_ = lean_st_ref_get(v___y_1160_);
v_env_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_env_1163_);
lean_dec(v___x_1162_);
v___x_1164_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1165_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_1164_, v___y_1159_);
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1186_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1186_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v_isExporting_1175_; 
v_isExporting_1175_ = lean_ctor_get_uint8(v_env_1163_, sizeof(void*)*8);
lean_dec_ref(v_env_1163_);
if (v_isExporting_1175_ == 0)
{
lean_dec(v_a_1166_);
lean_dec(v_id_1156_);
goto v___jp_1170_;
}
else
{
lean_object* v_val_1176_; uint8_t v___x_1177_; 
v_val_1176_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_val_1176_);
lean_dec(v_a_1166_);
v___x_1177_ = l_Lean_isPrivateName(v_id_1156_);
if (v___x_1177_ == 0)
{
lean_dec(v_val_1176_);
lean_dec(v_id_1156_);
goto v___jp_1170_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_unbox(v_val_1176_);
lean_dec(v_val_1176_);
if (v___x_1178_ == 0)
{
lean_dec(v_id_1156_);
goto v___jp_1170_;
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_del_object(v___x_1168_);
v___x_1179_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_MessageData_ofConstName(v_id_1156_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1179_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_1184_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1185_;
}
}
}
v___jp_1170_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_1194_, uint8_t v_enableLog_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_toCold_1202_; lean_object* v_env_1203_; lean_object* v_options_1204_; lean_object* v_currNamespace_1205_; lean_object* v_openDecls_1206_; lean_object* v___x_1207_; lean_object* v_env_1208_; lean_object* v_res_1209_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_toCold_1202_ = lean_ctor_get(v___y_1198_, 0);
v_env_1203_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1203_);
lean_dec(v___x_1201_);
v_options_1204_ = lean_ctor_get(v_toCold_1202_, 2);
v_currNamespace_1205_ = lean_ctor_get(v_toCold_1202_, 4);
v_openDecls_1206_ = lean_ctor_get(v_toCold_1202_, 5);
v___x_1207_ = lean_st_ref_get(v___y_1199_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
lean_inc(v_openDecls_1206_);
lean_inc(v_currNamespace_1205_);
v_res_1209_ = l_Lean_ResolveName_resolveGlobalName(v_env_1203_, v_options_1204_, v_currNamespace_1205_, v_openDecls_1206_, v_id_1194_);
if (v_enableLog_1195_ == 0)
{
lean_dec_ref(v_env_1208_);
goto v___jp_1210_;
}
else
{
uint8_t v_isExporting_1213_; 
v_isExporting_1213_ = lean_ctor_get_uint8(v_env_1208_, sizeof(void*)*8);
lean_dec_ref(v_env_1208_);
if (v_isExporting_1213_ == 0)
{
goto v___jp_1210_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1209_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v_fst_1216_; lean_object* v___x_1217_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v_fst_1216_ = lean_ctor_get(v_val_1215_, 0);
lean_inc(v_fst_1216_);
lean_dec(v_val_1215_);
v___x_1217_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_1216_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_res_1209_);
v___x_1222_ = lean_box(0);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
else
{
lean_dec_ref_known(v_a_1218_, 1);
lean_del_object(v___x_1220_);
goto v___jp_1210_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_res_1209_);
v_a_1227_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1217_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1217_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_dec(v___x_1214_);
goto v___jp_1210_;
}
}
}
v___jp_1210_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_res_1209_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_1235_, lean_object* v_enableLog_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_enableLog_boxed_1242_; lean_object* v_res_1243_; 
v_enableLog_boxed_1242_ = lean_unbox(v_enableLog_1236_);
v_res_1243_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_1235_, v_enableLog_boxed_1242_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_1248_, lean_object* v_filter_1249_, lean_object* v_view_x3f_1250_, lean_object* v_n_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1327_; 
if (lean_obj_tag(v_view_x3f_1250_) == 1)
{
lean_object* v_val_1354_; lean_object* v_imported_1355_; lean_object* v_ctx_1356_; lean_object* v_scopes_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_val_1354_ = lean_ctor_get(v_view_x3f_1250_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v_view_x3f_1250_, 1);
v_imported_1355_ = lean_ctor_get(v_val_1354_, 1);
v_ctx_1356_ = lean_ctor_get(v_val_1354_, 2);
v_scopes_1357_ = lean_ctor_get(v_val_1354_, 3);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_val_1354_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_val_1354_, 0);
lean_dec(v_unused_1366_);
v___x_1359_ = v_val_1354_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_scopes_1357_);
lean_inc(v_ctx_1356_);
lean_inc(v_imported_1355_);
lean_dec(v_val_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_n_1251_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_n_1251_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_imported_1355_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_ctx_1356_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_scopes_1357_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_MacroScopesView_review(v___x_1362_);
v___y_1327_ = v___x_1363_;
goto v___jp_1326_;
}
}
}
else
{
lean_dec(v_view_x3f_1250_);
v___y_1327_ = v_n_1251_;
goto v___jp_1326_;
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
v___jp_1260_:
{
lean_object* v___x_1263_; 
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___x_1263_ = lean_apply_5(v___y_1262_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1283_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec(v___y_1261_);
v___x_1268_ = lean_box(0);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_a_1264_, 0);
lean_dec(v_unused_1282_);
v___x_1273_ = v_a_1264_;
v_isShared_1274_ = v_isSharedCheck_1281_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v_a_1264_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1281_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___y_1261_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___y_1261_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1276_);
v___x_1278_ = v___x_1266_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v___y_1261_);
v_a_1284_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1263_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1263_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1292_:
{
lean_object* v___x_1295_; 
lean_inc_ref(v___y_1294_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___x_1295_ = lean_apply_5(v___y_1294_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1317_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1317_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1317_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
if (lean_obj_tag(v_a_1296_) == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec(v___y_1293_);
lean_dec_ref(v_filter_1249_);
v___x_1300_ = lean_box(0);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
else
{
lean_object* v___x_1304_; 
lean_dec_ref_known(v_a_1296_, 1);
lean_del_object(v___x_1298_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1293_);
v___x_1304_ = lean_apply_6(v_filter_1249_, v___y_1293_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; uint8_t v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___f_1307_; 
v___f_1307_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1261_ = v___y_1293_;
v___y_1262_ = v___f_1307_;
goto v___jp_1260_;
}
else
{
lean_object* v___f_1308_; 
v___f_1308_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1261_ = v___y_1293_;
v___y_1262_ = v___f_1308_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v___y_1293_);
v_a_1309_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1304_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1304_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v___y_1293_);
lean_dec_ref(v_filter_1249_);
v_a_1318_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1295_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1295_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
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
v___jp_1326_:
{
uint8_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = 0;
lean_inc(v___y_1327_);
v___x_1329_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_1327_, v___x_1328_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1345_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
if (lean_obj_tag(v_a_1330_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec(v___y_1327_);
lean_dec_ref(v_filter_1249_);
v___x_1334_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v_val_1338_; 
lean_del_object(v___x_1332_);
v_val_1338_ = lean_ctor_get(v_a_1330_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v_a_1330_, 1);
if (lean_obj_tag(v_val_1338_) == 1)
{
lean_object* v_head_1339_; lean_object* v_tail_1340_; 
v_head_1339_ = lean_ctor_get(v_val_1338_, 0);
lean_inc(v_head_1339_);
v_tail_1340_ = lean_ctor_get(v_val_1338_, 1);
lean_inc(v_tail_1340_);
lean_dec_ref_known(v_val_1338_, 2);
if (lean_obj_tag(v_tail_1340_) == 0)
{
lean_object* v_fst_1341_; uint8_t v___x_1342_; 
v_fst_1341_ = lean_ctor_get(v_head_1339_, 0);
lean_inc(v_fst_1341_);
lean_dec(v_head_1339_);
v___x_1342_ = lean_name_eq(v_fst_1341_, v_n_u2080_1248_);
lean_dec(v_fst_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___f_1343_; 
v___f_1343_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1293_ = v___y_1327_;
v___y_1294_ = v___f_1343_;
goto v___jp_1292_;
}
else
{
lean_object* v___f_1344_; 
v___f_1344_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1293_ = v___y_1327_;
v___y_1294_ = v___f_1344_;
goto v___jp_1292_;
}
}
else
{
lean_dec(v_tail_1340_);
lean_dec(v_head_1339_);
lean_dec(v___y_1327_);
lean_dec_ref(v_filter_1249_);
goto v___jp_1257_;
}
}
else
{
lean_dec(v_val_1338_);
lean_dec(v___y_1327_);
lean_dec_ref(v_filter_1249_);
goto v___jp_1257_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v___y_1327_);
lean_dec_ref(v_filter_1249_);
v_a_1346_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1329_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1329_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_1367_, lean_object* v_filter_1368_, lean_object* v_view_x3f_1369_, lean_object* v_n_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1367_, v_filter_1368_, v_view_x3f_1369_, v_n_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v_n_u2080_1367_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_1377_, lean_object* v_filter_1378_, lean_object* v_view_x3f_1379_, lean_object* v_as_x27_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
if (lean_obj_tag(v_as_x27_1380_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_view_x3f_1379_);
lean_dec_ref(v_filter_1378_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_b_1381_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v_head_1389_; lean_object* v_tail_1390_; lean_object* v_snd_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1429_; 
v_head_1389_ = lean_ctor_get(v_as_x27_1380_, 0);
v_tail_1390_ = lean_ctor_get(v_as_x27_1380_, 1);
v_snd_1391_ = lean_ctor_get(v_b_1381_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_b_1381_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_b_1381_, 0);
lean_dec(v_unused_1430_);
v___x_1393_ = v_b_1381_;
v_isShared_1394_ = v_isSharedCheck_1429_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_snd_1391_);
lean_dec(v_b_1381_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1429_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = l_Lean_Name_appendCore(v_head_1389_, v_snd_1391_);
lean_inc(v___x_1395_);
lean_inc(v_view_x3f_1379_);
lean_inc_ref(v_filter_1378_);
v___x_1396_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1377_, v_filter_1378_, v_view_x3f_1379_, v___x_1395_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1420_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1420_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1420_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_a_1397_) == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_del_object(v___x_1399_);
v___x_1401_ = lean_box(0);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1395_);
lean_ctor_set(v___x_1393_, 0, v___x_1401_);
v___x_1403_ = v___x_1393_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1395_);
v___x_1403_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
v_as_x27_1380_ = v_tail_1390_;
v_b_1381_ = v___x_1403_;
goto _start;
}
}
else
{
lean_object* v___x_1407_; 
lean_dec(v_view_x3f_1379_);
lean_dec_ref(v_filter_1378_);
lean_inc_ref(v_a_1397_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1395_);
lean_ctor_set(v___x_1393_, 0, v_a_1397_);
v___x_1407_ = v___x_1393_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1397_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1395_);
v___x_1407_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_a_1397_, 0);
lean_dec(v_unused_1418_);
v___x_1409_ = v_a_1397_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_a_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1407_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1412_);
v___x_1414_ = v___x_1399_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v___x_1395_);
lean_del_object(v___x_1393_);
lean_dec(v_view_x3f_1379_);
lean_dec_ref(v_filter_1378_);
v_a_1421_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1396_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1396_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_1431_, lean_object* v_filter_1432_, lean_object* v_view_x3f_1433_, lean_object* v_as_x27_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1431_, v_filter_1432_, v_view_x3f_1433_, v_as_x27_1434_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v_as_x27_1434_);
lean_dec(v_n_u2080_1431_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_1445_, lean_object* v_filter_1446_, lean_object* v_view_x3f_1447_, lean_object* v_n_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___y_1455_; uint8_t v___x_1496_; 
v___x_1496_ = l_Lean_Name_hasMacroScopes(v_n_1448_);
if (v___x_1496_ == 0)
{
lean_object* v___f_1497_; 
v___f_1497_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1455_ = v___f_1497_;
goto v___jp_1454_;
}
else
{
lean_object* v___f_1498_; 
v___f_1498_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1455_ = v___f_1498_;
goto v___jp_1454_;
}
v___jp_1454_:
{
lean_object* v___x_1456_; 
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
v___x_1456_ = lean_apply_5(v___y_1455_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, lean_box(0));
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1487_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1487_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1487_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
if (lean_obj_tag(v_a_1457_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec(v_n_1448_);
lean_dec(v_view_x3f_1447_);
lean_dec_ref(v_filter_1446_);
v___x_1461_ = lean_box(0);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref_known(v_a_1457_, 1);
lean_del_object(v___x_1459_);
v___x_1465_ = l_Lean_privateToUserName(v_n_1448_);
v___x_1466_ = l_Lean_Name_componentsRev(v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_1468_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1445_, v_filter_1446_, v_view_x3f_1447_, v___x_1466_, v___x_1467_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___x_1466_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1478_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_val_1473_; lean_object* v_fst_1474_; lean_object* v___x_1476_; 
v_val_1473_ = lean_ctor_get(v_a_1469_, 0);
lean_inc(v_val_1473_);
lean_dec(v_a_1469_);
v_fst_1474_ = lean_ctor_get(v_val_1473_, 0);
lean_inc(v_fst_1474_);
lean_dec(v_val_1473_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_fst_1474_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_fst_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_a_1479_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1468_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1468_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_n_1448_);
lean_dec(v_view_x3f_1447_);
lean_dec_ref(v_filter_1446_);
v_a_1488_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1456_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1456_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1499_, lean_object* v_filter_1500_, lean_object* v_view_x3f_1501_, lean_object* v_n_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1499_, v_filter_1500_, v_view_x3f_1501_, v_n_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v_n_u2080_1499_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1509_, lean_object* v_filter_1510_, lean_object* v_as_1511_, lean_object* v_i_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_array_get_size(v_as_1511_);
v___x_1519_ = lean_nat_dec_lt(v_i_1512_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v_i_1512_);
lean_dec_ref(v_filter_1510_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_array_fget_borrowed(v_as_1511_, v_i_1512_);
lean_inc(v___x_1523_);
lean_inc_ref(v_filter_1510_);
v___x_1524_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1509_, v_filter_1510_, v___x_1522_, v___x_1523_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
if (lean_obj_tag(v_a_1525_) == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_i_1512_, v___x_1526_);
lean_dec(v_i_1512_);
v_i_1512_ = v___x_1527_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1525_, 1);
lean_dec(v_i_1512_);
lean_dec_ref(v_filter_1510_);
return v___x_1524_;
}
}
else
{
lean_dec(v_i_1512_);
lean_dec_ref(v_filter_1510_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1529_, lean_object* v_filter_1530_, lean_object* v_as_1531_, lean_object* v_i_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1529_, v_filter_1530_, v_as_1531_, v_i_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_as_1531_);
lean_dec(v_n_u2080_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1539_, lean_object* v_as_1540_, size_t v_i_1541_, size_t v_stop_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v___y_1545_; uint8_t v___x_1549_; 
v___x_1549_ = lean_usize_dec_eq(v_i_1541_, v_stop_1542_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1550_ = lean_array_uget_borrowed(v_as_1540_, v_i_1541_);
v___x_1551_ = l_Lean_Name_getPrefix(v___x_1550_);
v___x_1552_ = l_Lean_Name_getPrefix(v_n_u2081_1539_);
v___x_1553_ = l_Lean_Name_isPrefixOf(v___x_1551_, v___x_1552_);
lean_dec(v___x_1552_);
lean_dec(v___x_1551_);
if (v___x_1553_ == 0)
{
v___y_1545_ = v_b_1543_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1554_; 
lean_inc(v___x_1550_);
v___x_1554_ = lean_array_push(v_b_1543_, v___x_1550_);
v___y_1545_ = v___x_1554_;
goto v___jp_1544_;
}
}
else
{
return v_b_1543_;
}
v___jp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1541_, v___x_1546_);
v_i_1541_ = v___x_1547_;
v_b_1543_ = v___y_1545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1555_, lean_object* v_as_1556_, lean_object* v_i_1557_, lean_object* v_stop_1558_, lean_object* v_b_1559_){
_start:
{
size_t v_i_boxed_1560_; size_t v_stop_boxed_1561_; lean_object* v_res_1562_; 
v_i_boxed_1560_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_stop_boxed_1561_ = lean_unbox_usize(v_stop_1558_);
lean_dec(v_stop_1558_);
v_res_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1555_, v_as_1556_, v_i_boxed_1560_, v_stop_boxed_1561_, v_b_1559_);
lean_dec_ref(v_as_1556_);
lean_dec(v_n_u2081_1555_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1565_, uint8_t v_fullNames_1566_, uint8_t v_allowHorizAliases_1567_, lean_object* v_filter_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_view_1574_; lean_object* v_name_1575_; lean_object* v_n_u2081_1576_; 
lean_inc(v_n_u2080_1565_);
v_view_1574_ = l_Lean_extractMacroScopes(v_n_u2080_1565_);
v_name_1575_ = lean_ctor_get(v_view_1574_, 0);
lean_inc(v_name_1575_);
v_n_u2081_1576_ = l_Lean_privateToUserName(v_name_1575_);
if (v_fullNames_1566_ == 0)
{
lean_object* v___x_1577_; lean_object* v_aliases_1579_; lean_object* v_env_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1577_ = lean_st_ref_get(v___y_1572_);
v_env_1594_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1594_);
lean_dec(v___x_1577_);
lean_inc(v_n_u2080_1565_);
v___x_1595_ = l_Lean_getRevAliases(v_env_1594_, v_n_u2080_1565_);
v___x_1596_ = lean_array_mk(v___x_1595_);
if (v_allowHorizAliases_1567_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = lean_array_get_size(v___x_1596_);
v___x_1599_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1600_ = lean_nat_dec_lt(v___x_1597_, v___x_1598_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v___x_1596_);
v_aliases_1579_ = v___x_1599_;
goto v___jp_1578_;
}
else
{
size_t v___x_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = lean_usize_of_nat(v___x_1598_);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1576_, v___x_1596_, v___x_1601_, v___x_1602_, v___x_1599_);
lean_dec_ref(v___x_1596_);
v_aliases_1579_ = v___x_1603_;
goto v___jp_1578_;
}
}
else
{
v_aliases_1579_ = v___x_1596_;
goto v___jp_1578_;
}
v___jp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1568_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1565_, v_filter_1568_, v_aliases_1579_, v___x_1580_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v_aliases_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
if (lean_obj_tag(v_a_1582_) == 0)
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1592_; 
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1581_, 0);
lean_dec(v_unused_1593_);
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
lean_ctor_set(v___x_1584_, 0, v_view_1574_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_view_1574_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = l_Lean_rootNamespace;
v___x_1589_ = l_Lean_Name_append(v___x_1588_, v_n_u2081_1576_);
v___x_1590_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1565_, v_filter_1568_, v___x_1587_, v___x_1589_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v_n_u2080_1565_);
return v___x_1590_;
}
}
}
else
{
lean_dec_ref_known(v_a_1582_, 1);
lean_dec(v_n_u2081_1576_);
lean_dec_ref(v_view_1574_);
lean_dec_ref(v_filter_1568_);
lean_dec(v_n_u2080_1565_);
return v___x_1581_;
}
}
else
{
lean_dec(v_n_u2081_1576_);
lean_dec_ref(v_view_1574_);
lean_dec_ref(v_filter_1568_);
lean_dec(v_n_u2080_1565_);
return v___x_1581_;
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_view_1574_);
lean_inc(v_n_u2081_1576_);
lean_inc_ref(v___x_1604_);
lean_inc_ref(v_filter_1568_);
v___x_1605_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1565_, v_filter_1568_, v___x_1604_, v_n_u2081_1576_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
if (lean_obj_tag(v_a_1606_) == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = l_Lean_rootNamespace;
v___x_1608_ = l_Lean_Name_append(v___x_1607_, v_n_u2081_1576_);
v___x_1609_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1565_, v_filter_1568_, v___x_1604_, v___x_1608_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v_n_u2080_1565_);
return v___x_1609_;
}
else
{
lean_dec_ref_known(v_a_1606_, 1);
lean_dec_ref_known(v___x_1604_, 1);
lean_dec(v_n_u2081_1576_);
lean_dec_ref(v_filter_1568_);
lean_dec(v_n_u2080_1565_);
return v___x_1605_;
}
}
else
{
lean_dec_ref_known(v___x_1604_, 1);
lean_dec(v_n_u2081_1576_);
lean_dec_ref(v_filter_1568_);
lean_dec(v_n_u2080_1565_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1610_, lean_object* v_fullNames_1611_, lean_object* v_allowHorizAliases_1612_, lean_object* v_filter_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v_fullNames_boxed_1619_; uint8_t v_allowHorizAliases_boxed_1620_; lean_object* v_res_1621_; 
v_fullNames_boxed_1619_ = lean_unbox(v_fullNames_1611_);
v_allowHorizAliases_boxed_1620_ = lean_unbox(v_allowHorizAliases_1612_);
v_res_1621_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1610_, v_fullNames_boxed_1619_, v_allowHorizAliases_boxed_1620_, v_filter_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1625_, uint8_t v_fullNames_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 0;
v___f_1633_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0));
v___x_1634_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1625_, v_fullNames_1626_, v___x_1632_, v___f_1633_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1635_, lean_object* v_fullNames_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
uint8_t v_fullNames_boxed_1642_; lean_object* v_res_1643_; 
v_fullNames_boxed_1642_ = lean_unbox(v_fullNames_1636_);
v_res_1643_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_n_u2080_1635_, v_fullNames_boxed_1642_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1643_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
lean_ctor_set(v___x_1649_, 2, v___x_1648_);
lean_ctor_set(v___x_1649_, 3, v___x_1648_);
lean_ctor_set(v___x_1649_, 4, v___x_1647_);
lean_ctor_set(v___x_1649_, 5, v___x_1647_);
lean_ctor_set(v___x_1649_, 6, v___x_1647_);
lean_ctor_set(v___x_1649_, 7, v___x_1647_);
lean_ctor_set(v___x_1649_, 8, v___x_1647_);
lean_ctor_set(v___x_1649_, 9, v___x_1647_);
lean_ctor_set(v___x_1649_, 10, v___x_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(32u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = ((size_t)5ULL);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = lean_unsigned_to_nat(32u);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1655_);
v___x_1657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1658_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1656_);
lean_ctor_set(v___x_1658_, 2, v___x_1654_);
lean_ctor_set(v___x_1658_, 3, v___x_1654_);
lean_ctor_set_usize(v___x_1658_, 4, v___x_1653_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = lean_box(1);
v___x_1660_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1661_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___x_1660_);
lean_ctor_set(v___x_1662_, 2, v___x_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_toCold_1668_; lean_object* v_env_1669_; lean_object* v_options_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1667_ = lean_st_ref_get(v___y_1665_);
v_toCold_1668_ = lean_ctor_get(v___y_1664_, 0);
v_env_1669_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_ref(v_env_1669_);
lean_dec(v___x_1667_);
v_options_1670_ = lean_ctor_get(v_toCold_1668_, 2);
v___x_1671_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1672_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1670_);
v___x_1673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1673_, 0, v_env_1669_);
lean_ctor_set(v___x_1673_, 1, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v___x_1672_);
lean_ctor_set(v___x_1673_, 3, v_options_1670_);
v___x_1674_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_msgData_1663_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_1681_, lean_object* v_msgData_1682_, uint8_t v_severity_1683_, uint8_t v_isSilent_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; lean_object* v___y_1693_; uint8_t v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; uint8_t v___y_1729_; uint8_t v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; uint8_t v___y_1755_; uint8_t v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1762_; lean_object* v___y_1763_; uint8_t v___y_1764_; lean_object* v___y_1765_; uint8_t v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; uint8_t v___x_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; uint8_t v___y_1778_; uint8_t v___y_1779_; lean_object* v___y_1780_; uint8_t v___y_1781_; uint8_t v___y_1783_; uint8_t v___x_1799_; 
v___x_1773_ = 2;
v___x_1799_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1683_, v___x_1773_);
if (v___x_1799_ == 0)
{
v___y_1783_ = v___x_1799_;
goto v___jp_1782_;
}
else
{
uint8_t v___x_1800_; 
lean_inc_ref(v_msgData_1682_);
v___x_1800_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1682_);
v___y_1783_ = v___x_1800_;
goto v___jp_1782_;
}
v___jp_1688_:
{
lean_object* v___x_1698_; lean_object* v_toCold_1699_; lean_object* v_currNamespace_1700_; lean_object* v_openDecls_1701_; lean_object* v_env_1702_; lean_object* v_nextMacroScope_1703_; lean_object* v_ngen_1704_; lean_object* v_auxDeclNGen_1705_; lean_object* v_traceState_1706_; lean_object* v_cache_1707_; lean_object* v_messages_1708_; lean_object* v_infoState_1709_; lean_object* v_snapshotTasks_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1724_; 
v___x_1698_ = lean_st_ref_take(v___y_1697_);
v_toCold_1699_ = lean_ctor_get(v___y_1696_, 0);
v_currNamespace_1700_ = lean_ctor_get(v_toCold_1699_, 4);
v_openDecls_1701_ = lean_ctor_get(v_toCold_1699_, 5);
v_env_1702_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1703_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1704_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1705_ = lean_ctor_get(v___x_1698_, 3);
v_traceState_1706_ = lean_ctor_get(v___x_1698_, 4);
v_cache_1707_ = lean_ctor_get(v___x_1698_, 5);
v_messages_1708_ = lean_ctor_get(v___x_1698_, 6);
v_infoState_1709_ = lean_ctor_get(v___x_1698_, 7);
v_snapshotTasks_1710_ = lean_ctor_get(v___x_1698_, 8);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1712_ = v___x_1698_;
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snapshotTasks_1710_);
lean_inc(v_infoState_1709_);
lean_inc(v_messages_1708_);
lean_inc(v_cache_1707_);
lean_inc(v_traceState_1706_);
lean_inc(v_auxDeclNGen_1705_);
lean_inc(v_ngen_1704_);
lean_inc(v_nextMacroScope_1703_);
lean_inc(v_env_1702_);
lean_dec(v___x_1698_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_inc(v_openDecls_1701_);
lean_inc(v_currNamespace_1700_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_currNamespace_1700_);
lean_ctor_set(v___x_1714_, 1, v_openDecls_1701_);
v___x_1715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___y_1695_);
lean_inc_ref(v___y_1693_);
lean_inc_ref(v___y_1690_);
v___x_1716_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1716_, 0, v___y_1690_);
lean_ctor_set(v___x_1716_, 1, v___y_1689_);
lean_ctor_set(v___x_1716_, 2, v___y_1691_);
lean_ctor_set(v___x_1716_, 3, v___y_1693_);
lean_ctor_set(v___x_1716_, 4, v___x_1715_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*5, v___y_1694_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*5 + 1, v___y_1692_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*5 + 2, v_isSilent_1684_);
v___x_1717_ = l_Lean_MessageLog_add(v___x_1716_, v_messages_1708_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 6, v___x_1717_);
v___x_1719_ = v___x_1712_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_env_1702_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_nextMacroScope_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_ngen_1704_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_auxDeclNGen_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_traceState_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_cache_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_infoState_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v_snapshotTasks_1710_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_st_ref_put(v___y_1697_, v___x_1719_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
}
}
v___jp_1725_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1749_; 
v___x_1734_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1682_);
v___x_1735_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v___x_1734_, v___y_1685_, v___y_1686_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1749_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1749_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_inc_ref_n(v___y_1731_, 2);
v___x_1740_ = l_Lean_FileMap_toPosition(v___y_1731_, v___y_1727_);
lean_dec(v___y_1727_);
v___x_1741_ = l_Lean_FileMap_toPosition(v___y_1731_, v___y_1733_);
lean_dec(v___y_1733_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1729_ == 0)
{
lean_del_object(v___x_1738_);
lean_dec_ref(v___y_1726_);
v___y_1689_ = v___x_1740_;
v___y_1690_ = v___y_1728_;
v___y_1691_ = v___x_1742_;
v___y_1692_ = v___y_1730_;
v___y_1693_ = v___x_1743_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v_a_1736_;
v___y_1696_ = v___y_1685_;
v___y_1697_ = v___y_1686_;
goto v___jp_1688_;
}
else
{
uint8_t v___x_1744_; 
lean_inc(v_a_1736_);
v___x_1744_ = l_Lean_MessageData_hasTag(v___y_1726_, v_a_1736_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1742_, 1);
lean_dec_ref(v___x_1740_);
lean_dec(v_a_1736_);
v___x_1745_ = lean_box(0);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1745_);
v___x_1747_ = v___x_1738_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
else
{
lean_del_object(v___x_1738_);
v___y_1689_ = v___x_1740_;
v___y_1690_ = v___y_1728_;
v___y_1691_ = v___x_1742_;
v___y_1692_ = v___y_1730_;
v___y_1693_ = v___x_1743_;
v___y_1694_ = v___y_1732_;
v___y_1695_ = v_a_1736_;
v___y_1696_ = v___y_1685_;
v___y_1697_ = v___y_1686_;
goto v___jp_1688_;
}
}
}
}
v___jp_1750_:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Syntax_getTailPos_x3f(v___y_1752_, v___y_1757_);
lean_dec(v___y_1752_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_inc(v___y_1758_);
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1758_;
v___y_1728_ = v___y_1753_;
v___y_1729_ = v___y_1756_;
v___y_1730_ = v___y_1755_;
v___y_1731_ = v___y_1754_;
v___y_1732_ = v___y_1757_;
v___y_1733_ = v___y_1758_;
goto v___jp_1725_;
}
else
{
lean_object* v_val_1760_; 
v_val_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1758_;
v___y_1728_ = v___y_1753_;
v___y_1729_ = v___y_1756_;
v___y_1730_ = v___y_1755_;
v___y_1731_ = v___y_1754_;
v___y_1732_ = v___y_1757_;
v___y_1733_ = v_val_1760_;
goto v___jp_1725_;
}
}
v___jp_1761_:
{
lean_object* v_ref_1769_; lean_object* v___x_1770_; 
v_ref_1769_ = l_Lean_replaceRef(v_ref_1681_, v___y_1767_);
v___x_1770_ = l_Lean_Syntax_getPos_x3f(v_ref_1769_, v___y_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___y_1751_ = v___y_1762_;
v___y_1752_ = v_ref_1769_;
v___y_1753_ = v___y_1763_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1768_;
v___y_1756_ = v___y_1764_;
v___y_1757_ = v___y_1766_;
v___y_1758_ = v___x_1771_;
goto v___jp_1750_;
}
else
{
lean_object* v_val_1772_; 
v_val_1772_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v___x_1770_, 1);
v___y_1751_ = v___y_1762_;
v___y_1752_ = v_ref_1769_;
v___y_1753_ = v___y_1763_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1768_;
v___y_1756_ = v___y_1764_;
v___y_1757_ = v___y_1766_;
v___y_1758_ = v_val_1772_;
goto v___jp_1750_;
}
}
v___jp_1774_:
{
if (v___y_1781_ == 0)
{
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1778_;
v___y_1765_ = v___y_1777_;
v___y_1766_ = v___y_1779_;
v___y_1767_ = v___y_1780_;
v___y_1768_ = v_severity_1683_;
goto v___jp_1761_;
}
else
{
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1778_;
v___y_1765_ = v___y_1777_;
v___y_1766_ = v___y_1779_;
v___y_1767_ = v___y_1780_;
v___y_1768_ = v___x_1773_;
goto v___jp_1761_;
}
}
v___jp_1782_:
{
if (v___y_1783_ == 0)
{
lean_object* v_toCold_1784_; lean_object* v_ref_1785_; uint8_t v_suppressElabErrors_1786_; lean_object* v_fileName_1787_; lean_object* v_fileMap_1788_; lean_object* v_options_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___f_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; 
v_toCold_1784_ = lean_ctor_get(v___y_1685_, 0);
v_ref_1785_ = lean_ctor_get(v___y_1685_, 2);
v_suppressElabErrors_1786_ = lean_ctor_get_uint8(v___y_1685_, sizeof(void*)*3 + 1);
v_fileName_1787_ = lean_ctor_get(v_toCold_1784_, 0);
v_fileMap_1788_ = lean_ctor_get(v_toCold_1784_, 1);
v_options_1789_ = lean_ctor_get(v_toCold_1784_, 2);
v___x_1790_ = lean_box(v_suppressElabErrors_1786_);
v___x_1791_ = lean_box(v___y_1783_);
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1792_, 0, v___x_1790_);
lean_closure_set(v___f_1792_, 1, v___x_1791_);
v___x_1793_ = 1;
v___x_1794_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1683_, v___x_1793_);
if (v___x_1794_ == 0)
{
v___y_1775_ = v___f_1792_;
v___y_1776_ = v_fileName_1787_;
v___y_1777_ = v_fileMap_1788_;
v___y_1778_ = v_suppressElabErrors_1786_;
v___y_1779_ = v___y_1783_;
v___y_1780_ = v_ref_1785_;
v___y_1781_ = v___x_1794_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = l_Lean_warningAsError;
v___x_1796_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_1789_, v___x_1795_);
v___y_1775_ = v___f_1792_;
v___y_1776_ = v_fileName_1787_;
v___y_1777_ = v_fileMap_1788_;
v___y_1778_ = v_suppressElabErrors_1786_;
v___y_1779_ = v___y_1783_;
v___y_1780_ = v_ref_1785_;
v___y_1781_ = v___x_1796_;
goto v___jp_1774_;
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v_msgData_1682_);
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1801_, lean_object* v_msgData_1802_, lean_object* v_severity_1803_, lean_object* v_isSilent_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_severity_boxed_1808_; uint8_t v_isSilent_boxed_1809_; lean_object* v_res_1810_; 
v_severity_boxed_1808_ = lean_unbox(v_severity_1803_);
v_isSilent_boxed_1809_ = lean_unbox(v_isSilent_1804_);
v_res_1810_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1801_, v_msgData_1802_, v_severity_boxed_1808_, v_isSilent_boxed_1809_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v_ref_1801_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1811_, uint8_t v_severity_1812_, uint8_t v_isSilent_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_ref_1817_; lean_object* v___x_1818_; 
v_ref_1817_ = lean_ctor_get(v___y_1814_, 2);
v___x_1818_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1817_, v_msgData_1811_, v_severity_1812_, v_isSilent_1813_, v___y_1814_, v___y_1815_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1819_, lean_object* v_severity_1820_, lean_object* v_isSilent_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_severity_boxed_1825_; uint8_t v_isSilent_boxed_1826_; lean_object* v_res_1827_; 
v_severity_boxed_1825_ = lean_unbox(v_severity_1820_);
v_isSilent_boxed_1826_ = lean_unbox(v_isSilent_1821_);
v_res_1827_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1819_, v_severity_boxed_1825_, v_isSilent_boxed_1826_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint8_t v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = 1;
v___x_1833_ = 0;
v___x_1834_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1828_, v___x_1832_, v___x_1833_, v___y_1829_, v___y_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msgData_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v_env_1844_; lean_object* v___x_1845_; lean_object* v_toEnvExtension_1846_; lean_object* v_asyncMode_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v_merged_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v___x_1843_ = lean_st_ref_get(v___y_1841_);
v_env_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_env_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1846_ = lean_ctor_get(v___x_1845_, 0);
v_asyncMode_1847_ = lean_ctor_get(v_toEnvExtension_1846_, 2);
v___x_1848_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1849_ = lean_box(0);
v___x_1850_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1848_, v___x_1845_, v_env_1844_, v_asyncMode_1847_, v___x_1849_);
v_merged_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1850_, 1);
lean_dec(v_unused_1860_);
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_merged_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v_merged_1851_);
lean_ctor_set(v___x_1853_, 0, v_o_1840_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_o_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_merged_1851_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_toCold_1868_; lean_object* v_options_1869_; lean_object* v___x_1870_; 
v_toCold_1868_ = lean_ctor_get(v___y_1865_, 0);
v_options_1869_ = lean_ctor_get(v_toCold_1868_, 2);
lean_inc_ref(v_options_1869_);
v___x_1870_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_options_1869_, v___y_1866_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_ref_1879_; lean_object* v___x_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_ref_1879_ = lean_ctor_get(v___y_1876_, 2);
v___x_1880_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1875_, v___y_1876_, v___y_1877_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_inc(v_ref_1879_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_ref_1879_);
lean_ctor_set(v___x_1885_, 1, v_a_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1895_, lean_object* v_i_1896_, lean_object* v_k_1897_){
_start:
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = lean_array_get_size(v_keys_1895_);
v___x_1899_ = lean_nat_dec_lt(v_i_1896_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec(v_i_1896_);
return v___x_1899_;
}
else
{
lean_object* v_k_x27_1900_; uint8_t v___x_1901_; 
v_k_x27_1900_ = lean_array_fget_borrowed(v_keys_1895_, v_i_1896_);
v___x_1901_ = l_Lean_instBEqExtraModUse_beq(v_k_1897_, v_k_x27_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_i_1896_, v___x_1902_);
lean_dec(v_i_1896_);
v_i_1896_ = v___x_1903_;
goto _start;
}
else
{
lean_dec(v_i_1896_);
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_1905_, lean_object* v_i_1906_, lean_object* v_k_1907_){
_start:
{
uint8_t v_res_1908_; lean_object* v_r_1909_; 
v_res_1908_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1905_, v_i_1906_, v_k_1907_);
lean_dec_ref(v_k_1907_);
lean_dec_ref(v_keys_1905_);
v_r_1909_ = lean_box(v_res_1908_);
return v_r_1909_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_1910_, size_t v_x_1911_, lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1910_) == 0)
{
lean_object* v_es_1913_; lean_object* v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; lean_object* v_j_1917_; lean_object* v___x_1918_; 
v_es_1913_ = lean_ctor_get(v_x_1910_, 0);
v___x_1914_ = lean_box(2);
v___x_1915_ = ((size_t)31ULL);
v___x_1916_ = lean_usize_land(v_x_1911_, v___x_1915_);
v_j_1917_ = lean_usize_to_nat(v___x_1916_);
v___x_1918_ = lean_array_get_borrowed(v___x_1914_, v_es_1913_, v_j_1917_);
lean_dec(v_j_1917_);
switch(lean_obj_tag(v___x_1918_))
{
case 0:
{
lean_object* v_key_1919_; uint8_t v___x_1920_; 
v_key_1919_ = lean_ctor_get(v___x_1918_, 0);
v___x_1920_ = l_Lean_instBEqExtraModUse_beq(v_x_1912_, v_key_1919_);
return v___x_1920_;
}
case 1:
{
lean_object* v_node_1921_; size_t v___x_1922_; size_t v___x_1923_; 
v_node_1921_ = lean_ctor_get(v___x_1918_, 0);
v___x_1922_ = ((size_t)5ULL);
v___x_1923_ = lean_usize_shift_right(v_x_1911_, v___x_1922_);
v_x_1910_ = v_node_1921_;
v_x_1911_ = v___x_1923_;
goto _start;
}
default: 
{
uint8_t v___x_1925_; 
v___x_1925_ = 0;
return v___x_1925_;
}
}
}
else
{
lean_object* v_ks_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v_ks_1926_ = lean_ctor_get(v_x_1910_, 0);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_1926_, v___x_1927_, v_x_1912_);
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
size_t v_x_45488__boxed_1932_; uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_x_45488__boxed_1932_ = lean_unbox_usize(v_x_1930_);
lean_dec(v_x_1930_);
v_res_1933_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1929_, v_x_45488__boxed_1932_, v_x_1931_);
lean_dec_ref(v_x_1931_);
lean_dec_ref(v_x_1929_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
uint64_t v___x_1937_; size_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = l_Lean_instHashableExtraModUse_hash(v_x_1936_);
v___x_1938_ = lean_uint64_to_usize(v___x_1937_);
v___x_1939_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1935_, v___x_1938_, v_x_1936_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1940_, lean_object* v_x_1941_){
_start:
{
uint8_t v_res_1942_; lean_object* v_r_1943_; 
v_res_1942_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1940_, v_x_1941_);
lean_dec_ref(v_x_1941_);
lean_dec_ref(v_x_1940_);
v_r_1943_ = lean_box(v_res_1942_);
return v_r_1943_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1944_; double v___x_1945_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_float_of_nat(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1948_, lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_ref_1953_; lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1999_; 
v_ref_1953_ = lean_ctor_get(v___y_1950_, 2);
v___x_1954_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1949_, v___y_1950_, v___y_1951_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1999_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1999_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v_traceState_1960_; lean_object* v_env_1961_; lean_object* v_nextMacroScope_1962_; lean_object* v_ngen_1963_; lean_object* v_auxDeclNGen_1964_; lean_object* v_cache_1965_; lean_object* v_messages_1966_; lean_object* v_infoState_1967_; lean_object* v_snapshotTasks_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1998_; 
v___x_1959_ = lean_st_ref_take(v___y_1951_);
v_traceState_1960_ = lean_ctor_get(v___x_1959_, 4);
v_env_1961_ = lean_ctor_get(v___x_1959_, 0);
v_nextMacroScope_1962_ = lean_ctor_get(v___x_1959_, 1);
v_ngen_1963_ = lean_ctor_get(v___x_1959_, 2);
v_auxDeclNGen_1964_ = lean_ctor_get(v___x_1959_, 3);
v_cache_1965_ = lean_ctor_get(v___x_1959_, 5);
v_messages_1966_ = lean_ctor_get(v___x_1959_, 6);
v_infoState_1967_ = lean_ctor_get(v___x_1959_, 7);
v_snapshotTasks_1968_ = lean_ctor_get(v___x_1959_, 8);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1970_ = v___x_1959_;
v_isShared_1971_ = v_isSharedCheck_1998_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_snapshotTasks_1968_);
lean_inc(v_infoState_1967_);
lean_inc(v_messages_1966_);
lean_inc(v_cache_1965_);
lean_inc(v_traceState_1960_);
lean_inc(v_auxDeclNGen_1964_);
lean_inc(v_ngen_1963_);
lean_inc(v_nextMacroScope_1962_);
lean_inc(v_env_1961_);
lean_dec(v___x_1959_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1998_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint64_t v_tid_1972_; lean_object* v_traces_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1997_; 
v_tid_1972_ = lean_ctor_get_uint64(v_traceState_1960_, sizeof(void*)*1);
v_traces_1973_ = lean_ctor_get(v_traceState_1960_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_traceState_1960_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1975_ = v_traceState_1960_;
v_isShared_1976_ = v_isSharedCheck_1997_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_traces_1973_);
lean_dec(v_traceState_1960_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1997_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; double v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1979_ = 0;
v___x_1980_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1981_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1981_, 0, v_cls_1948_);
lean_ctor_set(v___x_1981_, 1, v___x_1977_);
lean_ctor_set(v___x_1981_, 2, v___x_1980_);
lean_ctor_set_float(v___x_1981_, sizeof(void*)*3, v___x_1978_);
lean_ctor_set_float(v___x_1981_, sizeof(void*)*3 + 8, v___x_1978_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*3 + 16, v___x_1979_);
v___x_1982_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1983_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v_a_1955_);
lean_ctor_set(v___x_1983_, 2, v___x_1982_);
lean_inc(v_ref_1953_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_ref_1953_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_PersistentArray_push___redArg(v_traces_1973_, v___x_1984_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1985_);
v___x_1987_ = v___x_1975_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1985_);
lean_ctor_set_uint64(v_reuseFailAlloc_1996_, sizeof(void*)*1, v_tid_1972_);
v___x_1987_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_1987_);
v___x_1989_ = v___x_1970_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_env_1961_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_nextMacroScope_1962_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_ngen_1963_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_auxDeclNGen_1964_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_cache_1965_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_messages_1966_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v_infoState_1967_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v_snapshotTasks_1968_);
v___x_1989_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_st_ref_put(v___y_1951_, v___x_1989_);
v___x_1991_ = lean_box(0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1991_);
v___x_1993_ = v___x_1957_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_2000_, lean_object* v_msg_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2000_, v_msg_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2005_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_2009_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_2010_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2009_, v___x_2008_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2011_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
return v___x_2024_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_2026_ = l_Lean_stringToMessageData(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_cls_2029_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2030_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_2031_ = l_Lean_Name_append(v___x_2030_, v_cls_2029_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2042_, uint8_t v_isMeta_2043_, lean_object* v_hint_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v_env_2049_; uint8_t v_isExporting_2050_; lean_object* v___x_2051_; lean_object* v_env_2052_; lean_object* v___x_2053_; lean_object* v_entry_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___y_2059_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2048_ = lean_st_ref_get(v___y_2046_);
v_env_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2049_);
lean_dec(v___x_2048_);
v_isExporting_2050_ = lean_ctor_get_uint8(v_env_2049_, sizeof(void*)*8);
lean_dec_ref(v_env_2049_);
v___x_2051_ = lean_st_ref_get(v___y_2046_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2051_);
v___x_2053_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_2042_);
v_entry_2054_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2054_, 0, v_mod_2042_);
lean_ctor_set_uint8(v_entry_2054_, sizeof(void*)*1, v_isExporting_2050_);
lean_ctor_set_uint8(v_entry_2054_, sizeof(void*)*1 + 1, v_isMeta_2043_);
v___x_2055_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2056_ = lean_box(1);
v___x_2057_ = lean_box(0);
v___x_2084_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2053_, v___x_2055_, v_env_2052_, v___x_2056_, v___x_2057_);
v___x_2085_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2084_, v_entry_2054_);
lean_dec(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v_toCold_2086_; lean_object* v_options_2087_; uint8_t v_hasTrace_2088_; 
v_toCold_2086_ = lean_ctor_get(v___y_2045_, 0);
v_options_2087_ = lean_ctor_get(v_toCold_2086_, 2);
v_hasTrace_2088_ = lean_ctor_get_uint8(v_options_2087_, sizeof(void*)*1);
if (v_hasTrace_2088_ == 0)
{
lean_dec(v_hint_2044_);
lean_dec(v_mod_2042_);
v___y_2059_ = v___y_2046_;
goto v___jp_2058_;
}
else
{
lean_object* v_inheritedTraceOptions_2089_; lean_object* v_cls_2090_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_inheritedTraceOptions_2089_ = lean_ctor_get(v_toCold_2086_, 11);
v_cls_2090_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2110_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_2111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2089_, v_options_2087_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v_hint_2044_);
lean_dec(v_mod_2042_);
v___y_2059_ = v___y_2046_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2112_; lean_object* v___y_2114_; 
v___x_2112_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16);
if (v_isExporting_2050_ == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_2114_ = v___x_2121_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__22));
v___y_2114_ = v___x_2122_;
goto v___jp_2113_;
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_inc_ref(v___y_2114_);
v___x_2115_ = l_Lean_stringToMessageData(v___y_2114_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2112_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
if (v_isMeta_2043_ == 0)
{
lean_object* v___x_2119_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_2097_ = v___x_2118_;
v___y_2098_ = v___x_2119_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__20));
v___y_2097_ = v___x_2118_;
v___y_2098_ = v___x_2120_;
goto v___jp_2096_;
}
}
}
v___jp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___y_2092_);
lean_ctor_set(v___x_2094_, 1, v___y_2093_);
v___x_2095_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2090_, v___x_2094_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
v___y_2059_ = v___y_2046_;
goto v___jp_2058_;
}
else
{
lean_dec_ref_known(v_entry_2054_, 1);
return v___x_2095_;
}
}
v___jp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_inc_ref(v___y_2098_);
v___x_2099_ = l_Lean_stringToMessageData(v___y_2098_);
v___x_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___y_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___x_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_MessageData_ofName(v_mod_2042_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_Lean_Name_isAnonymous(v_hint_2044_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2107_ = l_Lean_MessageData_ofName(v_hint_2044_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___y_2092_ = v___x_2104_;
v___y_2093_ = v___x_2108_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2109_; 
lean_dec(v_hint_2044_);
v___x_2109_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___y_2092_ = v___x_2104_;
v___y_2093_ = v___x_2109_;
goto v___jp_2091_;
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec_ref_known(v_entry_2054_, 1);
lean_dec(v_hint_2044_);
lean_dec(v_mod_2042_);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v_toEnvExtension_2061_; lean_object* v_env_2062_; lean_object* v_nextMacroScope_2063_; lean_object* v_ngen_2064_; lean_object* v_auxDeclNGen_2065_; lean_object* v_traceState_2066_; lean_object* v_messages_2067_; lean_object* v_infoState_2068_; lean_object* v_snapshotTasks_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2082_; 
v___x_2060_ = lean_st_ref_take(v___y_2059_);
v_toEnvExtension_2061_ = lean_ctor_get(v___x_2055_, 0);
v_env_2062_ = lean_ctor_get(v___x_2060_, 0);
v_nextMacroScope_2063_ = lean_ctor_get(v___x_2060_, 1);
v_ngen_2064_ = lean_ctor_get(v___x_2060_, 2);
v_auxDeclNGen_2065_ = lean_ctor_get(v___x_2060_, 3);
v_traceState_2066_ = lean_ctor_get(v___x_2060_, 4);
v_messages_2067_ = lean_ctor_get(v___x_2060_, 6);
v_infoState_2068_ = lean_ctor_get(v___x_2060_, 7);
v_snapshotTasks_2069_ = lean_ctor_get(v___x_2060_, 8);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2060_, 5);
lean_dec(v_unused_2083_);
v___x_2071_ = v___x_2060_;
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snapshotTasks_2069_);
lean_inc(v_infoState_2068_);
lean_inc(v_messages_2067_);
lean_inc(v_traceState_2066_);
lean_inc(v_auxDeclNGen_2065_);
lean_inc(v_ngen_2064_);
lean_inc(v_nextMacroScope_2063_);
lean_inc(v_env_2062_);
lean_dec(v___x_2060_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_asyncMode_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v_asyncMode_2073_ = lean_ctor_get(v_toEnvExtension_2061_, 2);
v___x_2074_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2055_, v_env_2062_, v_entry_2054_, v_asyncMode_2073_, v___x_2057_);
v___x_2075_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 5, v___x_2075_);
lean_ctor_set(v___x_2071_, 0, v___x_2074_);
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_nextMacroScope_2063_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_ngen_2064_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_auxDeclNGen_2065_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_traceState_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 5, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2081_, 6, v_messages_2067_);
lean_ctor_set(v_reuseFailAlloc_2081_, 7, v_infoState_2068_);
lean_ctor_set(v_reuseFailAlloc_2081_, 8, v_snapshotTasks_2069_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_st_ref_put(v___y_2059_, v___x_2077_);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2125_, lean_object* v_isMeta_2126_, lean_object* v_hint_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v_isMeta_boxed_2131_; lean_object* v_res_2132_; 
v_isMeta_boxed_2131_ = lean_unbox(v_isMeta_2126_);
v_res_2132_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_mod_2125_, v_isMeta_boxed_2131_, v_hint_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2133_, lean_object* v_declName_2134_, lean_object* v_as_2135_, size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_lt(v_i_2137_, v_sz_2136_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_declName_2134_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_b_2138_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; lean_object* v_modules_2145_; lean_object* v___x_2146_; lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v_toImport_2149_; lean_object* v_module_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2144_ = l_Lean_Environment_header(v___x_2133_);
v_modules_2145_ = lean_ctor_get(v___x_2144_, 3);
lean_inc_ref(v_modules_2145_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2147_ = lean_array_uget_borrowed(v_as_2135_, v_i_2137_);
v___x_2148_ = lean_array_get(v___x_2146_, v_modules_2145_, v_a_2147_);
lean_dec_ref(v_modules_2145_);
v_toImport_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_ref(v_toImport_2149_);
lean_dec(v___x_2148_);
v_module_2150_ = lean_ctor_get(v_toImport_2149_, 0);
lean_inc(v_module_2150_);
lean_dec_ref(v_toImport_2149_);
v___x_2151_ = 0;
lean_inc(v_declName_2134_);
v___x_2152_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2150_, v___x_2151_, v_declName_2134_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; 
lean_dec_ref_known(v___x_2152_, 1);
v___x_2153_ = lean_box(0);
v___x_2154_ = ((size_t)1ULL);
v___x_2155_ = lean_usize_add(v_i_2137_, v___x_2154_);
v_i_2137_ = v___x_2155_;
v_b_2138_ = v___x_2153_;
goto _start;
}
else
{
lean_dec(v_declName_2134_);
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2157_, lean_object* v_declName_2158_, lean_object* v_as_2159_, lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v___x_2157_, v_declName_2158_, v_as_2159_, v_sz_boxed_2166_, v_i_boxed_2167_, v_b_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v_as_2159_);
lean_dec_ref(v___x_2157_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v_key_2172_; lean_object* v_value_2173_; lean_object* v_tail_2174_; uint8_t v___x_2175_; 
v_key_2172_ = lean_ctor_get(v_x_2170_, 0);
v_value_2173_ = lean_ctor_get(v_x_2170_, 1);
v_tail_2174_ = lean_ctor_get(v_x_2170_, 2);
v___x_2175_ = lean_name_eq(v_key_2172_, v_a_2169_);
if (v___x_2175_ == 0)
{
v_x_2170_ = v_tail_2174_;
goto _start;
}
else
{
lean_object* v___x_2177_; 
lean_inc(v_value_2173_);
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_value_2173_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2178_, v_x_2179_);
lean_dec(v_x_2179_);
lean_dec(v_a_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_buckets_2183_; lean_object* v___x_2184_; uint64_t v___y_2186_; 
v_buckets_2183_ = lean_ctor_get(v_m_2181_, 1);
v___x_2184_ = lean_array_get_size(v_buckets_2183_);
if (lean_obj_tag(v_a_2182_) == 0)
{
uint64_t v___x_2200_; 
v___x_2200_ = 1723ULL;
v___y_2186_ = v___x_2200_;
goto v___jp_2185_;
}
else
{
uint64_t v_hash_2201_; 
v_hash_2201_ = lean_ctor_get_uint64(v_a_2182_, sizeof(void*)*2);
v___y_2186_ = v_hash_2201_;
goto v___jp_2185_;
}
v___jp_2185_:
{
uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v_fold_2189_; uint64_t v___x_2190_; uint64_t v___x_2191_; uint64_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2187_ = 32ULL;
v___x_2188_ = lean_uint64_shift_right(v___y_2186_, v___x_2187_);
v_fold_2189_ = lean_uint64_xor(v___y_2186_, v___x_2188_);
v___x_2190_ = 16ULL;
v___x_2191_ = lean_uint64_shift_right(v_fold_2189_, v___x_2190_);
v___x_2192_ = lean_uint64_xor(v_fold_2189_, v___x_2191_);
v___x_2193_ = lean_uint64_to_usize(v___x_2192_);
v___x_2194_ = lean_usize_of_nat(v___x_2184_);
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_sub(v___x_2194_, v___x_2195_);
v___x_2197_ = lean_usize_land(v___x_2193_, v___x_2196_);
v___x_2198_ = lean_array_uget_borrowed(v_buckets_2183_, v___x_2197_);
v___x_2199_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2182_, v___x_2198_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_m_2202_);
return v_res_2204_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1));
v___x_2208_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0));
v___x_2209_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(lean_object* v_declName_2212_, uint8_t v_isMeta_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v_env_2221_; lean_object* v___y_2223_; lean_object* v___x_2236_; 
v___x_2217_ = lean_st_ref_get(v___y_2215_);
v_env_2221_ = lean_ctor_get(v___x_2217_, 0);
lean_inc_ref(v_env_2221_);
lean_dec(v___x_2217_);
v___x_2236_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2221_, v_declName_2212_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_dec_ref(v_env_2221_);
lean_dec(v_declName_2212_);
goto v___jp_2218_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2238_; lean_object* v_modules_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l_Lean_Environment_header(v_env_2221_);
v_modules_2239_ = lean_ctor_get(v___x_2238_, 3);
lean_inc_ref(v_modules_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_array_get_size(v_modules_2239_);
v___x_2241_ = lean_nat_dec_lt(v_val_2237_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_dec_ref(v_modules_2239_);
lean_dec(v_val_2237_);
lean_dec_ref(v_env_2221_);
lean_dec(v_declName_2212_);
goto v___jp_2218_;
}
else
{
lean_object* v___x_2242_; lean_object* v_env_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___y_2247_; 
v___x_2242_ = lean_st_ref_get(v___y_2215_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2);
v___x_2245_ = lean_array_fget(v_modules_2239_, v_val_2237_);
lean_dec(v_val_2237_);
lean_dec_ref(v_modules_2239_);
if (v_isMeta_2213_ == 0)
{
lean_dec_ref(v_env_2243_);
v___y_2247_ = v_isMeta_2213_;
goto v___jp_2246_;
}
else
{
uint8_t v___x_2258_; 
lean_inc(v_declName_2212_);
v___x_2258_ = l_Lean_isMarkedMeta(v_env_2243_, v_declName_2212_);
if (v___x_2258_ == 0)
{
v___y_2247_ = v_isMeta_2213_;
goto v___jp_2246_;
}
else
{
uint8_t v___x_2259_; 
v___x_2259_ = 0;
v___y_2247_ = v___x_2259_;
goto v___jp_2246_;
}
}
v___jp_2246_:
{
lean_object* v_toImport_2248_; lean_object* v_module_2249_; lean_object* v___x_2250_; 
v_toImport_2248_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_ref(v_toImport_2248_);
lean_dec(v___x_2245_);
v_module_2249_ = lean_ctor_get(v_toImport_2248_, 0);
lean_inc(v_module_2249_);
lean_dec_ref(v_toImport_2248_);
lean_inc(v_declName_2212_);
v___x_2250_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2249_, v___y_2247_, v_declName_2212_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref_known(v___x_2250_, 1);
v___x_2251_ = l_Lean_indirectModUseExt;
v___x_2252_ = lean_box(1);
v___x_2253_ = lean_box(0);
lean_inc_ref(v_env_2221_);
v___x_2254_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2244_, v___x_2251_, v_env_2221_, v___x_2252_, v___x_2253_);
v___x_2255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2254_, v_declName_2212_);
lean_dec(v___x_2254_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__3));
v___y_2223_ = v___x_2256_;
goto v___jp_2222_;
}
else
{
lean_object* v_val_2257_; 
v_val_2257_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v___x_2255_, 1);
v___y_2223_ = v_val_2257_;
goto v___jp_2222_;
}
}
else
{
lean_dec_ref(v_env_2221_);
lean_dec(v_declName_2212_);
return v___x_2250_;
}
}
}
}
v___jp_2218_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
v___jp_2222_:
{
lean_object* v___x_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v___x_2224_ = lean_box(0);
v_sz_2225_ = lean_array_size(v___y_2223_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v_env_2221_, v_declName_2212_, v___y_2223_, v_sz_2225_, v___x_2226_, v___x_2224_, v___y_2214_, v___y_2215_);
lean_dec_ref(v___y_2223_);
lean_dec_ref(v_env_2221_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v___x_2227_, 0);
lean_dec(v_unused_2235_);
v___x_2229_ = v___x_2227_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v___x_2227_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2224_);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2224_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
return v___x_2227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_2260_, lean_object* v_isMeta_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_isMeta_boxed_2265_; lean_object* v_res_2266_; 
v_isMeta_boxed_2265_ = lean_unbox(v_isMeta_2261_);
v_res_2266_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_declName_2260_, v_isMeta_boxed_2265_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v_res_2266_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2271_ = l_Lean_MessageData_ofFormat(v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2276_ = l_Lean_MessageData_ofFormat(v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2285_ = l_Lean_stringToMessageData(v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2290_ = l_Lean_MessageData_ofFormat(v___x_2289_);
return v___x_2290_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2292_ = l_Lean_MessageData_hint_x27(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2295_ = l_Lean_stringToMessageData(v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2300_ = l_Lean_MessageData_ofFormat(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2315_ = l_Lean_MessageData_ofFormat(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2316_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = lean_box(1);
v___x_2320_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2321_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
lean_ctor_set(v___x_2322_, 2, v___x_2319_);
return v___x_2322_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_ctor_set(v___x_2327_, 2, v___x_2326_);
lean_ctor_set(v___x_2327_, 3, v___x_2326_);
lean_ctor_set(v___x_2327_, 4, v___x_2325_);
lean_ctor_set(v___x_2327_, 5, v___x_2325_);
lean_ctor_set(v___x_2327_, 6, v___x_2325_);
lean_ctor_set(v___x_2327_, 7, v___x_2325_);
lean_ctor_set(v___x_2327_, 8, v___x_2325_);
lean_ctor_set(v___x_2327_, 9, v___x_2325_);
lean_ctor_set(v___x_2327_, 10, v___x_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2329_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
lean_ctor_set(v___x_2329_, 2, v___x_2328_);
lean_ctor_set(v___x_2329_, 3, v___x_2328_);
lean_ctor_set(v___x_2329_, 4, v___x_2328_);
lean_ctor_set(v___x_2329_, 5, v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
lean_ctor_set(v___x_2331_, 2, v___x_2330_);
lean_ctor_set(v___x_2331_, 3, v___x_2330_);
lean_ctor_set(v___x_2331_, 4, v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2355_ = l_Lean_stringToMessageData(v___x_2354_);
return v___x_2355_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2358_ = l_Lean_stringToMessageData(v___x_2357_);
return v___x_2358_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2364_ = l_Lean_stringToMessageData(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2367_ = l_Lean_stringToMessageData(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v___f_2373_, uint8_t v___x_2374_, lean_object* v___x_2375_, lean_object* v___x_2376_, lean_object* v_a_2377_, lean_object* v_declName_2378_, lean_object* v_stx_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_hint_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; 
v___x_2389_ = l_Lean_Name_mkStr2(v___x_2371_, v___x_2372_);
lean_inc(v_stx_2379_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_stx_2379_, v___x_2389_);
lean_dec(v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v_stx_2379_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2499_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2500_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2499_, v___y_2380_, v___y_2381_);
return v___x_2500_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v_val_2512_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; uint8_t v_a_2559_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; uint8_t v___y_2626_; lean_object* v_msg_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v_a_2653_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v_a_2798_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_since_x3f_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v_typeChanged_x3f_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2854_; lean_object* v_text_x3f_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v_id_x3f_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2880_ = l_Lean_Syntax_getArg(v_stx_2379_, v___x_2502_);
v___x_2881_ = l_Lean_Syntax_isNone(v___x_2880_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
lean_inc(v___x_2880_);
v___x_2882_ = l_Lean_Syntax_matchesNull(v___x_2880_, v___x_2502_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v___x_2880_);
lean_dec(v_stx_2379_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2883_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2884_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2883_, v___y_2380_, v___y_2381_);
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = l_Lean_Syntax_getArg(v___x_2880_, v___x_2501_);
lean_dec(v___x_2880_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v_id_x3f_2868_ = v___x_2886_;
v___y_2869_ = v___y_2380_;
v___y_2870_ = v___y_2381_;
goto v___jp_2867_;
}
}
else
{
lean_object* v___x_2887_; 
lean_dec(v___x_2880_);
v___x_2887_ = lean_box(0);
v_id_x3f_2868_ = v___x_2887_;
v___y_2869_ = v___y_2380_;
v___y_2870_ = v___y_2381_;
goto v___jp_2867_;
}
v___jp_2503_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2513_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2514_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___f_2373_);
v___x_2518_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2514_);
lean_ctor_set(v___x_2518_, 1, v___x_2515_);
lean_ctor_set(v___x_2518_, 2, v___x_2515_);
lean_ctor_set(v___x_2518_, 3, v___x_2515_);
lean_ctor_set(v___x_2518_, 4, v___x_2516_);
lean_ctor_set(v___x_2518_, 5, v___x_2517_);
lean_inc(v_val_2512_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_val_2512_);
lean_ctor_set(v___x_2519_, 1, v_val_2512_);
v___x_2520_ = l_Lean_Syntax_ofRange(v___x_2519_, v___x_2390_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
v___x_2522_ = 4;
v___x_2523_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2523_, 0, v___x_2518_);
lean_ctor_set(v___x_2523_, 1, v___x_2521_);
lean_ctor_set(v___x_2523_, 2, v___x_2515_);
lean_ctor_set_uint8(v___x_2523_, sizeof(void*)*3, v___x_2522_);
v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2525_ = lean_array_push(v___x_2524_, v___x_2523_);
v___x_2526_ = l_Lean_MessageData_hint(v___x_2513_, v___x_2525_, v___x_2515_, v___x_2515_, v___x_2374_, v___y_2508_, v___y_2511_);
lean_dec_ref(v___x_2525_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___y_2459_ = v___y_2505_;
v___y_2460_ = v___y_2504_;
v___y_2461_ = v___y_2507_;
v___y_2462_ = v___y_2506_;
v___y_2463_ = v___y_2510_;
v___y_2464_ = v___y_2509_;
v_hint_2465_ = v_a_2527_;
v___y_2466_ = v___y_2508_;
v___y_2467_ = v___y_2511_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
v_a_2528_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2526_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2526_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
v___jp_2536_:
{
if (lean_obj_tag(v___y_2538_) == 0)
{
lean_dec_ref(v___f_2373_);
v___y_2490_ = v___y_2537_;
v___y_2491_ = v___y_2538_;
v___y_2492_ = v___y_2540_;
v___y_2493_ = v___y_2539_;
v___y_2494_ = v___y_2541_;
v___y_2495_ = v___y_2543_;
v___y_2496_ = v___y_2542_;
v___y_2497_ = v___y_2544_;
goto v___jp_2489_;
}
else
{
lean_object* v_val_2545_; lean_object* v___x_2546_; 
v_val_2545_ = lean_ctor_get(v___y_2538_, 0);
v___x_2546_ = l_Lean_Syntax_getTailPos_x3f(v_val_2545_, v___x_2390_);
if (lean_obj_tag(v___x_2546_) == 1)
{
lean_object* v_val_2547_; 
v_val_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_val_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___y_2504_ = v___y_2537_;
v___y_2505_ = v___y_2538_;
v___y_2506_ = v___y_2540_;
v___y_2507_ = v___y_2539_;
v___y_2508_ = v___y_2541_;
v___y_2509_ = v___y_2543_;
v___y_2510_ = v___y_2542_;
v___y_2511_ = v___y_2544_;
v_val_2512_ = v_val_2547_;
goto v___jp_2503_;
}
else
{
lean_dec(v___x_2546_);
lean_dec_ref(v___f_2373_);
v___y_2490_ = v___y_2537_;
v___y_2491_ = v___y_2538_;
v___y_2492_ = v___y_2540_;
v___y_2493_ = v___y_2539_;
v___y_2494_ = v___y_2541_;
v___y_2495_ = v___y_2543_;
v___y_2496_ = v___y_2542_;
v___y_2497_ = v___y_2544_;
goto v___jp_2489_;
}
}
}
v___jp_2548_:
{
if (v_a_2559_ == 0)
{
if (lean_obj_tag(v___y_2554_) == 0)
{
if (v___y_2558_ == 0)
{
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2549_;
v___y_2443_ = v___y_2552_;
v___y_2444_ = v___y_2551_;
v___y_2445_ = v___y_2555_;
v___y_2446_ = v___y_2553_;
v___y_2447_ = v___y_2557_;
goto v___jp_2441_;
}
else
{
if (lean_obj_tag(v___y_2552_) == 0)
{
v___y_2537_ = v___y_2550_;
v___y_2538_ = v___y_2549_;
v___y_2539_ = v___y_2551_;
v___y_2540_ = v___y_2552_;
v___y_2541_ = v___y_2553_;
v___y_2542_ = v___y_2555_;
v___y_2543_ = v___y_2556_;
v___y_2544_ = v___y_2557_;
goto v___jp_2536_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2561_; 
v_val_2560_ = lean_ctor_get(v___y_2552_, 0);
v___x_2561_ = l_Lean_Syntax_getTailPos_x3f(v_val_2560_, v___x_2390_);
if (lean_obj_tag(v___x_2561_) == 0)
{
v___y_2537_ = v___y_2550_;
v___y_2538_ = v___y_2549_;
v___y_2539_ = v___y_2551_;
v___y_2540_ = v___y_2552_;
v___y_2541_ = v___y_2553_;
v___y_2542_ = v___y_2555_;
v___y_2543_ = v___y_2556_;
v___y_2544_ = v___y_2557_;
goto v___jp_2536_;
}
else
{
lean_object* v_val_2562_; 
v_val_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___y_2504_ = v___y_2550_;
v___y_2505_ = v___y_2549_;
v___y_2506_ = v___y_2552_;
v___y_2507_ = v___y_2551_;
v___y_2508_ = v___y_2553_;
v___y_2509_ = v___y_2556_;
v___y_2510_ = v___y_2555_;
v___y_2511_ = v___y_2557_;
v_val_2512_ = v_val_2562_;
goto v___jp_2503_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2554_, 1);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2549_;
v___y_2443_ = v___y_2552_;
v___y_2444_ = v___y_2551_;
v___y_2445_ = v___y_2555_;
v___y_2446_ = v___y_2553_;
v___y_2447_ = v___y_2557_;
goto v___jp_2441_;
}
}
else
{
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___f_2373_);
if (lean_obj_tag(v___y_2554_) == 0)
{
v___y_2442_ = v___y_2549_;
v___y_2443_ = v___y_2552_;
v___y_2444_ = v___y_2551_;
v___y_2445_ = v___y_2555_;
v___y_2446_ = v___y_2553_;
v___y_2447_ = v___y_2557_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec_ref_known(v___y_2554_, 1);
v___x_2563_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2564_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2563_, v___y_2553_, v___y_2557_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_dec_ref_known(v___x_2564_, 1);
v___y_2442_ = v___y_2549_;
v___y_2443_ = v___y_2552_;
v___y_2444_ = v___y_2551_;
v___y_2445_ = v___y_2555_;
v___y_2446_ = v___y_2553_;
v___y_2447_ = v___y_2557_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v___y_2555_);
lean_dec(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v___y_2549_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2584_; 
lean_inc_ref(v___y_2580_);
v___x_2584_ = l_Lean_Environment_find_x3f(v___y_2580_, v_declName_2378_, v___x_2374_);
if (lean_obj_tag(v___x_2584_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; 
v_val_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = l_Lean_Environment_find_x3f(v___y_2580_, v___y_2575_, v___x_2374_);
if (lean_obj_tag(v___x_2586_) == 1)
{
lean_object* v_val_2587_; uint8_t v___x_2588_; uint8_t v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; uint64_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = 1;
v___x_2589_ = 0;
v___x_2590_ = 2;
v___x_2591_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2591_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 1, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 2, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 3, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 4, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 5, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 6, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 7, v___x_2374_);
lean_ctor_set_uint8(v___x_2591_, 8, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 9, v___x_2588_);
lean_ctor_set_uint8(v___x_2591_, 10, v___x_2589_);
lean_ctor_set_uint8(v___x_2591_, 11, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 12, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 13, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 14, v___x_2590_);
lean_ctor_set_uint8(v___x_2591_, 15, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 16, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 17, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 18, v___y_2581_);
lean_ctor_set_uint8(v___x_2591_, 19, v___x_2374_);
v___x_2592_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set_uint64(v___x_2593_, sizeof(void*)*1, v___x_2592_);
v___x_2594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2595_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2596_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2597_ = lean_box(0);
lean_inc(v___x_2375_);
v___x_2598_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2598_, 0, v___x_2593_);
lean_ctor_set(v___x_2598_, 1, v___x_2375_);
lean_ctor_set(v___x_2598_, 2, v___x_2595_);
lean_ctor_set(v___x_2598_, 3, v___x_2596_);
lean_ctor_set(v___x_2598_, 4, v___x_2597_);
lean_ctor_set(v___x_2598_, 5, v___x_2501_);
lean_ctor_set(v___x_2598_, 6, v___x_2597_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*7, v___x_2374_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*7 + 1, v___x_2374_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*7 + 2, v___x_2374_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*7 + 3, v___x_2390_);
v___x_2599_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2600_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2601_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2600_);
lean_ctor_set(v___x_2602_, 2, v___x_2375_);
lean_ctor_set(v___x_2602_, 3, v___x_2594_);
lean_ctor_set(v___x_2602_, 4, v___x_2601_);
v___x_2603_ = lean_st_mk_ref(v___x_2602_);
v___x_2604_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2585_, v_val_2587_, v___x_2598_, v___x_2603_, v___y_2582_, v___y_2583_);
lean_dec_ref_known(v___x_2598_, 7);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_st_ref_get(v___x_2603_);
lean_dec(v___x_2603_);
lean_dec(v___x_2606_);
v___x_2607_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
v___y_2549_ = v___y_2574_;
v___y_2550_ = v_val_2587_;
v___y_2551_ = v___y_2577_;
v___y_2552_ = v___y_2576_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2578_;
v___y_2555_ = v___y_2579_;
v___y_2556_ = v_val_2585_;
v___y_2557_ = v___y_2583_;
v___y_2558_ = v___y_2581_;
v_a_2559_ = v___x_2607_;
goto v___jp_2548_;
}
else
{
lean_dec(v___x_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2608_; uint8_t v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2609_ = lean_unbox(v_a_2608_);
lean_dec(v_a_2608_);
v___y_2549_ = v___y_2574_;
v___y_2550_ = v_val_2587_;
v___y_2551_ = v___y_2577_;
v___y_2552_ = v___y_2576_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2578_;
v___y_2555_ = v___y_2579_;
v___y_2556_ = v_val_2585_;
v___y_2557_ = v___y_2583_;
v___y_2558_ = v___y_2581_;
v_a_2559_ = v___x_2609_;
goto v___jp_2548_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_val_2587_);
lean_dec(v_val_2585_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2574_);
lean_dec_ref(v___f_2373_);
v_a_2610_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2604_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2604_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_dec(v___x_2586_);
lean_dec(v_val_2585_);
lean_dec(v___y_2578_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2574_;
v___y_2443_ = v___y_2576_;
v___y_2444_ = v___y_2577_;
v___y_2445_ = v___y_2579_;
v___y_2446_ = v___y_2582_;
v___y_2447_ = v___y_2583_;
goto v___jp_2441_;
}
}
else
{
lean_dec(v___x_2584_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2578_);
lean_dec(v___y_2575_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2574_;
v___y_2443_ = v___y_2576_;
v___y_2444_ = v___y_2577_;
v___y_2445_ = v___y_2579_;
v___y_2446_ = v___y_2582_;
v___y_2447_ = v___y_2583_;
goto v___jp_2441_;
}
}
v___jp_2618_:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msg_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_dec_ref_known(v___x_2630_, 1);
v___y_2574_ = v___y_2619_;
v___y_2575_ = v___y_2620_;
v___y_2576_ = v___y_2622_;
v___y_2577_ = v___y_2621_;
v___y_2578_ = v___y_2624_;
v___y_2579_ = v___y_2623_;
v___y_2580_ = v___y_2625_;
v___y_2581_ = v___y_2626_;
v___y_2582_ = v___y_2628_;
v___y_2583_ = v___y_2629_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec(v_declName_2378_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
v___jp_2639_:
{
if (lean_obj_tag(v_a_2653_) == 1)
{
lean_object* v_val_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2684_; 
v_val_2654_ = lean_ctor_get(v_a_2653_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2656_ = v_a_2653_;
v_isShared_2657_ = v_isSharedCheck_2684_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_val_2654_);
lean_dec(v_a_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2684_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2658_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___y_2641_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_Name_toString(v_val_2654_, v___x_2390_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_ctor_set(v___x_2665_, 2, v___x_2664_);
lean_ctor_set(v___x_2665_, 3, v___x_2664_);
lean_ctor_set(v___x_2665_, 4, v___x_2664_);
lean_ctor_set(v___x_2665_, 5, v___x_2664_);
v___x_2666_ = 0;
v___x_2667_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2664_);
lean_ctor_set(v___x_2667_, 2, v___x_2664_);
lean_ctor_set_uint8(v___x_2667_, sizeof(void*)*3, v___x_2666_);
v___x_2668_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2669_ = lean_array_push(v___x_2668_, v___x_2667_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___y_2644_);
v___x_2671_ = v___x_2656_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___y_2644_);
v___x_2671_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_MessageData_hint(v___x_2661_, v___x_2669_, v___x_2671_, v___x_2664_, v___x_2374_, v___y_2646_, v___y_2648_);
lean_dec_ref(v___x_2669_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2640_);
lean_ctor_set(v___x_2674_, 1, v_a_2673_);
v___y_2619_ = v___y_2647_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___y_2649_;
v___y_2622_ = v___y_2650_;
v___y_2623_ = v___y_2651_;
v___y_2624_ = v___y_2643_;
v___y_2625_ = v___y_2652_;
v___y_2626_ = v___y_2645_;
v_msg_2627_ = v___x_2674_;
v___y_2628_ = v___y_2646_;
v___y_2629_ = v___y_2648_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec(v___y_2647_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2640_);
lean_dec(v_declName_2378_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2675_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2672_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2672_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2653_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2641_);
v___y_2619_ = v___y_2647_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___y_2649_;
v___y_2622_ = v___y_2650_;
v___y_2623_ = v___y_2651_;
v___y_2624_ = v___y_2643_;
v___y_2625_ = v___y_2652_;
v___y_2626_ = v___y_2645_;
v_msg_2627_ = v___y_2640_;
v___y_2628_ = v___y_2646_;
v___y_2629_ = v___y_2648_;
goto v___jp_2618_;
}
}
v___jp_2685_:
{
if (lean_obj_tag(v___y_2690_) == 1)
{
lean_object* v_val_2693_; lean_object* v___x_2694_; 
v_val_2693_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_val_2693_);
v___x_2694_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_val_2693_, v___x_2374_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
lean_dec_ref_known(v___x_2694_, 1);
v___x_2695_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_2691_, v___y_2692_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_Linter_linter_deprecated;
v___x_2698_ = l_Lean_Linter_getLinterValue(v___x_2697_, v_a_2696_);
lean_dec(v_a_2696_);
if (v___x_2698_ == 0)
{
lean_dec(v___y_2689_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2686_;
v___y_2443_ = v___y_2688_;
v___y_2444_ = v___y_2687_;
v___y_2445_ = v___y_2690_;
v___y_2446_ = v___y_2691_;
v___y_2447_ = v___y_2692_;
goto v___jp_2441_;
}
else
{
lean_object* v___x_2699_; lean_object* v_toCold_2700_; lean_object* v_env_2701_; lean_object* v_options_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
lean_inc(v_val_2693_);
v___x_2699_ = lean_st_ref_get(v___y_2692_);
v_toCold_2700_ = lean_ctor_get(v___y_2691_, 0);
v_env_2701_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_ref(v_env_2701_);
lean_dec(v___x_2699_);
v_options_2702_ = lean_ctor_get(v_toCold_2700_, 2);
v___x_2703_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2704_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_2702_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_dec_ref(v___x_2376_);
v___y_2574_ = v___y_2686_;
v___y_2575_ = v_val_2693_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2687_;
v___y_2578_ = v___y_2689_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v_env_2701_;
v___y_2581_ = v___x_2698_;
v___y_2582_ = v___y_2691_;
v___y_2583_ = v___y_2692_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2705_; 
lean_inc(v_val_2693_);
lean_inc_ref(v_env_2701_);
v___x_2705_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2376_, v_a_2377_, v___x_2374_, v_env_2701_, v_val_2693_);
if (lean_obj_tag(v___x_2705_) == 1)
{
lean_object* v_val_2706_; lean_object* v_name_2707_; lean_object* v_newName_x3f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_val_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_val_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v_name_2707_ = lean_ctor_get(v___x_2703_, 0);
v_newName_x3f_2708_ = lean_ctor_get(v_val_2706_, 0);
lean_inc(v_newName_x3f_2708_);
lean_dec(v_val_2706_);
v___x_2709_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_name_2707_);
v___x_2710_ = l_Lean_MessageData_ofName(v_name_2707_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_note(v___x_2713_);
if (lean_obj_tag(v_newName_x3f_2708_) == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2715_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2693_);
v___x_2716_ = l_Lean_MessageData_ofConstName(v_val_2693_, v___x_2390_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
lean_inc(v_declName_2378_);
v___x_2720_ = l_Lean_MessageData_ofConstName(v_declName_2378_, v___x_2390_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v___x_2714_);
v___x_2725_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2724_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_dec_ref_known(v___x_2725_, 1);
v___y_2574_ = v___y_2686_;
v___y_2575_ = v_val_2693_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2687_;
v___y_2578_ = v___y_2689_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v_env_2701_;
v___y_2581_ = v___x_2698_;
v___y_2582_ = v___y_2691_;
v___y_2583_ = v___y_2692_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v_env_2701_);
lean_dec_ref_known(v___y_2690_, 1);
lean_dec(v_val_2693_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v_declName_2378_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_val_2734_; uint8_t v___x_2735_; 
v_val_2734_ = lean_ctor_get(v_newName_x3f_2708_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v_newName_x3f_2708_, 1);
v___x_2735_ = lean_name_eq(v_val_2734_, v_val_2693_);
if (v___x_2735_ == 0)
{
if (v___x_2704_ == 0)
{
lean_dec(v_val_2734_);
lean_dec_ref(v___x_2714_);
v___y_2574_ = v___y_2686_;
v___y_2575_ = v_val_2693_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2687_;
v___y_2578_ = v___y_2689_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v_env_2701_;
v___y_2581_ = v___x_2698_;
v___y_2582_ = v___y_2691_;
v___y_2583_ = v___y_2692_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2693_);
v___x_2737_ = l_Lean_MessageData_ofConstName(v_val_2693_, v___x_2390_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
lean_inc(v_val_2734_);
v___x_2741_ = l_Lean_MessageData_ofConstName(v_val_2734_, v___x_2390_);
lean_inc_ref_n(v___x_2741_, 2);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc(v_declName_2378_);
v___x_2745_ = l_Lean_MessageData_ofConstName(v_declName_2378_, v___x_2390_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v___x_2741_);
v___x_2750_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___x_2714_);
if (lean_obj_tag(v___y_2686_) == 1)
{
lean_object* v_val_2753_; lean_object* v___x_2754_; 
v_val_2753_ = lean_ctor_get(v___y_2686_, 0);
v___x_2754_ = l_Lean_Syntax_getRange_x3f(v_val_2753_, v___x_2390_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref(v___x_2741_);
lean_dec(v_val_2734_);
v___y_2619_ = v___y_2686_;
v___y_2620_ = v_val_2693_;
v___y_2621_ = v___y_2687_;
v___y_2622_ = v___y_2688_;
v___y_2623_ = v___y_2690_;
v___y_2624_ = v___y_2689_;
v___y_2625_ = v_env_2701_;
v___y_2626_ = v___x_2698_;
v_msg_2627_ = v___x_2752_;
v___y_2628_ = v___y_2691_;
v___y_2629_ = v___y_2692_;
goto v___jp_2618_;
}
else
{
uint8_t v___x_2755_; uint8_t v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; uint64_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_inc(v_val_2753_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2755_ = 1;
v___x_2756_ = 0;
v___x_2757_ = 2;
v___x_2758_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2758_, 0, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 1, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 2, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 3, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 4, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 5, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 6, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 7, v___x_2735_);
lean_ctor_set_uint8(v___x_2758_, 8, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 9, v___x_2755_);
lean_ctor_set_uint8(v___x_2758_, 10, v___x_2756_);
lean_ctor_set_uint8(v___x_2758_, 11, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 12, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 13, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 14, v___x_2757_);
lean_ctor_set_uint8(v___x_2758_, 15, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 16, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 17, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 18, v___x_2704_);
lean_ctor_set_uint8(v___x_2758_, 19, v___x_2735_);
v___x_2759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set_uint64(v___x_2760_, sizeof(void*)*1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2762_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2763_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2764_ = lean_box(0);
lean_inc_n(v___x_2375_, 2);
v___x_2765_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2765_, 0, v___x_2760_);
lean_ctor_set(v___x_2765_, 1, v___x_2375_);
lean_ctor_set(v___x_2765_, 2, v___x_2762_);
lean_ctor_set(v___x_2765_, 3, v___x_2763_);
lean_ctor_set(v___x_2765_, 4, v___x_2764_);
lean_ctor_set(v___x_2765_, 5, v___x_2501_);
lean_ctor_set(v___x_2765_, 6, v___x_2764_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*7, v___x_2374_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*7 + 1, v___x_2374_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*7 + 2, v___x_2374_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*7 + 3, v___x_2390_);
v___x_2766_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2767_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2768_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2767_);
lean_ctor_set(v___x_2769_, 2, v___x_2375_);
lean_ctor_set(v___x_2769_, 3, v___x_2761_);
lean_ctor_set(v___x_2769_, 4, v___x_2768_);
v___x_2770_ = lean_st_mk_ref(v___x_2769_);
v___x_2771_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_val_2734_, v___x_2374_, v___x_2765_, v___x_2770_, v___y_2691_, v___y_2692_);
lean_dec_ref_known(v___x_2765_, 7);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = lean_st_ref_get(v___x_2770_);
lean_dec(v___x_2770_);
lean_dec(v___x_2773_);
v___y_2640_ = v___x_2752_;
v___y_2641_ = v___x_2741_;
v___y_2642_ = v_val_2693_;
v___y_2643_ = v___y_2689_;
v___y_2644_ = v_val_2753_;
v___y_2645_ = v___x_2698_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2686_;
v___y_2648_ = v___y_2692_;
v___y_2649_ = v___y_2687_;
v___y_2650_ = v___y_2688_;
v___y_2651_ = v___y_2690_;
v___y_2652_ = v_env_2701_;
v_a_2653_ = v_a_2772_;
goto v___jp_2639_;
}
else
{
lean_dec(v___x_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2774_; 
v_a_2774_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2771_, 1);
v___y_2640_ = v___x_2752_;
v___y_2641_ = v___x_2741_;
v___y_2642_ = v_val_2693_;
v___y_2643_ = v___y_2689_;
v___y_2644_ = v_val_2753_;
v___y_2645_ = v___x_2698_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2686_;
v___y_2648_ = v___y_2692_;
v___y_2649_ = v___y_2687_;
v___y_2650_ = v___y_2688_;
v___y_2651_ = v___y_2690_;
v___y_2652_ = v_env_2701_;
v_a_2653_ = v_a_2774_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_val_2753_);
lean_dec_ref_known(v___y_2686_, 1);
lean_dec_ref_known(v___x_2752_, 2);
lean_dec_ref(v___x_2741_);
lean_dec_ref(v_env_2701_);
lean_dec_ref_known(v___y_2690_, 1);
lean_dec(v_val_2693_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v_declName_2378_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2775_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2771_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2771_);
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
}
}
else
{
lean_dec_ref(v___x_2741_);
lean_dec(v_val_2734_);
v___y_2619_ = v___y_2686_;
v___y_2620_ = v_val_2693_;
v___y_2621_ = v___y_2687_;
v___y_2622_ = v___y_2688_;
v___y_2623_ = v___y_2690_;
v___y_2624_ = v___y_2689_;
v___y_2625_ = v_env_2701_;
v___y_2626_ = v___x_2698_;
v_msg_2627_ = v___x_2752_;
v___y_2628_ = v___y_2691_;
v___y_2629_ = v___y_2692_;
goto v___jp_2618_;
}
}
}
else
{
lean_dec(v_val_2734_);
lean_dec_ref(v___x_2714_);
v___y_2574_ = v___y_2686_;
v___y_2575_ = v_val_2693_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2687_;
v___y_2578_ = v___y_2689_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v_env_2701_;
v___y_2581_ = v___x_2698_;
v___y_2582_ = v___y_2691_;
v___y_2583_ = v___y_2692_;
goto v___jp_2573_;
}
}
}
else
{
lean_dec(v___x_2705_);
v___y_2574_ = v___y_2686_;
v___y_2575_ = v_val_2693_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2687_;
v___y_2578_ = v___y_2689_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v_env_2701_;
v___y_2581_ = v___x_2698_;
v___y_2582_ = v___y_2691_;
v___y_2583_ = v___y_2692_;
goto v___jp_2573_;
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref_known(v___y_2690_, 1);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2783_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2694_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2694_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
else
{
lean_dec(v___y_2689_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___y_2442_ = v___y_2686_;
v___y_2443_ = v___y_2688_;
v___y_2444_ = v___y_2687_;
v___y_2445_ = v___y_2690_;
v___y_2446_ = v___y_2691_;
v___y_2447_ = v___y_2692_;
goto v___jp_2441_;
}
}
v___jp_2791_:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
lean_inc(v_declName_2378_);
v___x_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2799_, 0, v_declName_2378_);
v___x_2800_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_a_2798_, v___x_2799_);
lean_dec_ref_known(v___x_2799_, 1);
if (v___x_2800_ == 0)
{
v___y_2686_ = v___y_2792_;
v___y_2687_ = v___y_2794_;
v___y_2688_ = v___y_2795_;
v___y_2689_ = v___y_2797_;
v___y_2690_ = v_a_2798_;
v___y_2691_ = v___y_2793_;
v___y_2692_ = v___y_2796_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2792_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2801_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2802_ = l_Lean_MessageData_ofConstName(v_declName_2378_, v___x_2390_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2805_, v___y_2793_, v___y_2796_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
v___jp_2815_:
{
if (lean_obj_tag(v___y_2816_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_box(0);
v___y_2792_ = v___y_2816_;
v___y_2793_ = v___y_2820_;
v___y_2794_ = v_since_x3f_2819_;
v___y_2795_ = v___y_2817_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2818_;
v_a_2798_ = v___x_2822_;
goto v___jp_2791_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_val_2823_ = lean_ctor_get(v___y_2816_, 0);
v___x_2824_ = lean_box(0);
lean_inc(v_val_2823_);
v___x_2825_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2823_, v___x_2824_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2826_);
v___y_2792_ = v___y_2816_;
v___y_2793_ = v___y_2820_;
v___y_2794_ = v_since_x3f_2819_;
v___y_2795_ = v___y_2817_;
v___y_2796_ = v___y_2821_;
v___y_2797_ = v___y_2818_;
v_a_2798_ = v___x_2827_;
goto v___jp_2791_;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref_known(v___y_2816_, 1);
lean_dec(v_since_x3f_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v_a_2828_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2825_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2825_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
v___jp_2836_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = lean_unsigned_to_nat(4u);
v___x_2844_ = l_Lean_Syntax_getArg(v_stx_2379_, v___x_2843_);
lean_dec(v_stx_2379_);
v___x_2845_ = l_Lean_Syntax_isNone(v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2846_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2844_);
v___x_2847_ = l_Lean_Syntax_matchesNull(v___x_2844_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec(v___x_2844_);
lean_dec(v_typeChanged_x3f_2840_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2848_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2849_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2848_, v___y_2841_, v___y_2842_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = l_Lean_Syntax_getArg(v___x_2844_, v___y_2839_);
lean_dec(v___x_2844_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
v___y_2816_ = v___y_2837_;
v___y_2817_ = v___y_2838_;
v___y_2818_ = v_typeChanged_x3f_2840_;
v_since_x3f_2819_ = v___x_2851_;
v___y_2820_ = v___y_2841_;
v___y_2821_ = v___y_2842_;
goto v___jp_2815_;
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v___x_2844_);
v___x_2852_ = lean_box(0);
v___y_2816_ = v___y_2837_;
v___y_2817_ = v___y_2838_;
v___y_2818_ = v_typeChanged_x3f_2840_;
v_since_x3f_2819_ = v___x_2852_;
v___y_2820_ = v___y_2841_;
v___y_2821_ = v___y_2842_;
goto v___jp_2815_;
}
}
v___jp_2853_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2858_ = lean_unsigned_to_nat(3u);
v___x_2859_ = l_Lean_Syntax_getArg(v_stx_2379_, v___x_2858_);
v___x_2860_ = l_Lean_Syntax_isNone(v___x_2859_);
if (v___x_2860_ == 0)
{
uint8_t v___x_2861_; 
lean_inc(v___x_2859_);
v___x_2861_ = l_Lean_Syntax_matchesNull(v___x_2859_, v___x_2502_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec(v___x_2859_);
lean_dec(v_text_x3f_2855_);
lean_dec(v___y_2854_);
lean_dec(v_stx_2379_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2862_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2863_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2862_, v___y_2856_, v___y_2857_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = l_Lean_Syntax_getArg(v___x_2859_, v___x_2501_);
lean_dec(v___x_2859_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
v___y_2837_ = v___y_2854_;
v___y_2838_ = v_text_x3f_2855_;
v___y_2839_ = v___x_2858_;
v_typeChanged_x3f_2840_ = v___x_2865_;
v___y_2841_ = v___y_2856_;
v___y_2842_ = v___y_2857_;
goto v___jp_2836_;
}
}
else
{
lean_object* v___x_2866_; 
lean_dec(v___x_2859_);
v___x_2866_ = lean_box(0);
v___y_2837_ = v___y_2854_;
v___y_2838_ = v_text_x3f_2855_;
v___y_2839_ = v___x_2858_;
v_typeChanged_x3f_2840_ = v___x_2866_;
v___y_2841_ = v___y_2856_;
v___y_2842_ = v___y_2857_;
goto v___jp_2836_;
}
}
v___jp_2867_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(2u);
v___x_2872_ = l_Lean_Syntax_getArg(v_stx_2379_, v___x_2871_);
v___x_2873_ = l_Lean_Syntax_isNone(v___x_2872_);
if (v___x_2873_ == 0)
{
uint8_t v___x_2874_; 
lean_inc(v___x_2872_);
v___x_2874_ = l_Lean_Syntax_matchesNull(v___x_2872_, v___x_2502_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec(v___x_2872_);
lean_dec(v_id_x3f_2868_);
lean_dec(v_stx_2379_);
lean_dec(v_declName_2378_);
lean_dec_ref(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec_ref(v___f_2373_);
v___x_2875_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2876_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2875_, v___y_2869_, v___y_2870_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = l_Lean_Syntax_getArg(v___x_2872_, v___x_2501_);
lean_dec(v___x_2872_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
v___y_2854_ = v_id_x3f_2868_;
v_text_x3f_2855_ = v___x_2878_;
v___y_2856_ = v___y_2869_;
v___y_2857_ = v___y_2870_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2879_; 
lean_dec(v___x_2872_);
v___x_2879_ = lean_box(0);
v___y_2854_ = v_id_x3f_2868_;
v_text_x3f_2855_ = v___x_2879_;
v___y_2856_ = v___y_2869_;
v___y_2857_ = v___y_2870_;
goto v___jp_2853_;
}
}
}
v___jp_2383_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2387_, 0, v___y_2384_);
lean_ctor_set(v___x_2387_, 1, v___y_2386_);
lean_ctor_set(v___x_2387_, 2, v___y_2385_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
v___jp_2391_:
{
if (lean_obj_tag(v___y_2393_) == 0)
{
if (v___x_2390_ == 0)
{
v___y_2384_ = v___y_2392_;
v___y_2385_ = v___y_2393_;
v___y_2386_ = v___y_2394_;
goto v___jp_2383_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2398_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2397_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_dec_ref_known(v___x_2398_, 1);
v___y_2384_ = v___y_2392_;
v___y_2385_ = v___y_2393_;
v___y_2386_ = v___y_2394_;
goto v___jp_2383_;
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v___y_2394_);
lean_dec(v___y_2392_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
else
{
v___y_2384_ = v___y_2392_;
v___y_2385_ = v___y_2393_;
v___y_2386_ = v___y_2394_;
goto v___jp_2383_;
}
}
v___jp_2407_:
{
if (lean_obj_tag(v___y_2408_) == 0)
{
if (v___x_2390_ == 0)
{
v___y_2392_ = v___y_2411_;
v___y_2393_ = v___y_2413_;
v___y_2394_ = v___y_2412_;
v___y_2395_ = v___y_2410_;
v___y_2396_ = v___y_2409_;
goto v___jp_2391_;
}
else
{
if (lean_obj_tag(v___y_2412_) == 0)
{
if (v___x_2390_ == 0)
{
v___y_2392_ = v___y_2411_;
v___y_2393_ = v___y_2413_;
v___y_2394_ = v___y_2412_;
v___y_2395_ = v___y_2410_;
v___y_2396_ = v___y_2409_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2415_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2414_, v___y_2410_, v___y_2409_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
v___y_2392_ = v___y_2411_;
v___y_2393_ = v___y_2413_;
v___y_2394_ = v___y_2412_;
v___y_2395_ = v___y_2410_;
v___y_2396_ = v___y_2409_;
goto v___jp_2391_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v___y_2413_);
lean_dec(v___y_2411_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
v___y_2392_ = v___y_2411_;
v___y_2393_ = v___y_2413_;
v___y_2394_ = v___y_2412_;
v___y_2395_ = v___y_2410_;
v___y_2396_ = v___y_2409_;
goto v___jp_2391_;
}
}
}
else
{
lean_dec_ref_known(v___y_2408_, 1);
v___y_2392_ = v___y_2411_;
v___y_2393_ = v___y_2413_;
v___y_2394_ = v___y_2412_;
v___y_2395_ = v___y_2410_;
v___y_2396_ = v___y_2409_;
goto v___jp_2391_;
}
}
v___jp_2424_:
{
if (lean_obj_tag(v___y_2427_) == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_box(0);
v___y_2408_ = v___y_2425_;
v___y_2409_ = v___y_2426_;
v___y_2410_ = v___y_2428_;
v___y_2411_ = v___y_2429_;
v___y_2412_ = v___y_2430_;
v___y_2413_ = v___x_2431_;
goto v___jp_2407_;
}
else
{
lean_object* v_val_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_val_2432_ = lean_ctor_get(v___y_2427_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___y_2427_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___y_2427_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_val_2432_);
lean_dec(v___y_2427_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = l_Lean_TSyntax_getString(v_val_2432_);
lean_dec(v_val_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
v___y_2408_ = v___y_2425_;
v___y_2409_ = v___y_2426_;
v___y_2410_ = v___y_2428_;
v___y_2411_ = v___y_2429_;
v___y_2412_ = v___y_2430_;
v___y_2413_ = v___x_2438_;
goto v___jp_2407_;
}
}
}
}
v___jp_2441_:
{
if (lean_obj_tag(v___y_2443_) == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_box(0);
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2447_;
v___y_2427_ = v___y_2444_;
v___y_2428_ = v___y_2446_;
v___y_2429_ = v___y_2445_;
v___y_2430_ = v___x_2448_;
goto v___jp_2424_;
}
else
{
lean_object* v_val_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
v_val_2449_ = lean_ctor_get(v___y_2443_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___y_2443_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2451_ = v___y_2443_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_val_2449_);
lean_dec(v___y_2443_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_TSyntax_getString(v_val_2449_);
lean_dec(v_val_2449_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2447_;
v___y_2427_ = v___y_2444_;
v___y_2428_ = v___y_2446_;
v___y_2429_ = v___y_2445_;
v___y_2430_ = v___x_2455_;
goto v___jp_2424_;
}
}
}
}
v___jp_2458_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2468_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2469_ = l_Lean_ConstantInfo_type(v___y_2460_);
lean_dec_ref(v___y_2460_);
v___x_2470_ = l_Lean_indentExpr(v___x_2469_);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2468_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = l_Lean_ConstantInfo_type(v___y_2464_);
lean_dec_ref(v___y_2464_);
v___x_2475_ = l_Lean_indentExpr(v___x_2474_);
v___x_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2473_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v_hint_2465_);
v___x_2480_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2479_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_dec_ref_known(v___x_2480_, 1);
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___y_2462_;
v___y_2444_ = v___y_2461_;
v___y_2445_ = v___y_2463_;
v___y_2446_ = v___y_2466_;
v___y_2447_ = v___y_2467_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2459_);
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2489_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___y_2459_ = v___y_2491_;
v___y_2460_ = v___y_2490_;
v___y_2461_ = v___y_2493_;
v___y_2462_ = v___y_2492_;
v___y_2463_ = v___y_2496_;
v___y_2464_ = v___y_2495_;
v_hint_2465_ = v___x_2498_;
v___y_2466_ = v___y_2494_;
v___y_2467_ = v___y_2497_;
goto v___jp_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_2888_, lean_object* v___x_2889_, lean_object* v___f_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v_a_2894_, lean_object* v_declName_2895_, lean_object* v_stx_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v___x_46386__boxed_2900_; lean_object* v_res_2901_; 
v___x_46386__boxed_2900_ = lean_unbox(v___x_2891_);
v_res_2901_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_2888_, v___x_2889_, v___f_2890_, v___x_46386__boxed_2900_, v___x_2892_, v___x_2893_, v_a_2894_, v_declName_2895_, v_stx_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_a_2894_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; 
v___x_2921_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2922_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2923_ = 0;
v___f_2924_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2925_ = l_Lean_registerParametricAttributeExt___redArg(v___x_2922_, v___x_2923_, v___f_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___f_2927_; lean_object* v___f_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___f_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc_n(v_a_2926_, 2);
lean_dec_ref_known(v___x_2925_, 1);
v___f_2927_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___f_2928_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2929_ = lean_box(1);
v___x_2930_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_2931_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2932_ = lean_box(v___x_2923_);
v___f_2933_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_2933_, 0, v___x_2921_);
lean_closure_set(v___f_2933_, 1, v___x_2931_);
lean_closure_set(v___f_2933_, 2, v___f_2927_);
lean_closure_set(v___f_2933_, 3, v___x_2932_);
lean_closure_set(v___f_2933_, 4, v___x_2929_);
lean_closure_set(v___f_2933_, 5, v___x_2930_);
lean_closure_set(v___f_2933_, 6, v_a_2926_);
v___x_2934_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2935_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___f_2933_);
lean_ctor_set(v___x_2935_, 2, v___f_2928_);
lean_ctor_set(v___x_2935_, 3, v___f_2924_);
lean_ctor_set_uint8(v___x_2935_, sizeof(void*)*4, v___x_2923_);
v___x_2936_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_2935_, v_a_2926_);
return v___x_2936_;
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2925_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2925_);
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2947_, lean_object* v_msg_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_2948_, v___y_2949_, v___y_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2953_, lean_object* v_msg_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(v_00_u03b1_2953_, v_msg_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_2959_, v___y_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(v_o_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_2969_, lean_object* v_m_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2970_, v_a_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_2973_, v_m_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_m_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2977_, lean_object* v_x_2978_, lean_object* v_x_2979_){
_start:
{
uint8_t v___x_2980_; 
v___x_2980_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2978_, v_x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_){
_start:
{
uint8_t v_res_2984_; lean_object* v_r_2985_; 
v_res_2984_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_2981_, v_x_2982_, v_x_2983_);
lean_dec_ref(v_x_2983_);
lean_dec_ref(v_x_2982_);
v_r_2985_ = lean_box(v_res_2984_);
return v_r_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_2986_, lean_object* v_a_2987_, lean_object* v_x_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2987_, v_x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2990_, lean_object* v_a_2991_, lean_object* v_x_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_2990_, v_a_2991_, v_x_2992_);
lean_dec(v_x_2992_);
lean_dec(v_a_2991_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_2994_, lean_object* v_t_2995_, lean_object* v_k_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_2995_, v_k_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_2998_, lean_object* v_t_2999_, lean_object* v_k_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_2998_, v_t_2999_, v_k_3000_);
lean_dec(v_k_3000_);
lean_dec(v_t_2999_);
return v_res_3001_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_3002_, lean_object* v_x_3003_, size_t v_x_3004_, lean_object* v_x_3005_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_3003_, v_x_3004_, v_x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3007_, lean_object* v_x_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_){
_start:
{
size_t v_x_47667__boxed_3011_; uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_x_47667__boxed_3011_ = lean_unbox_usize(v_x_3009_);
lean_dec(v_x_3009_);
v_res_3012_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_3007_, v_x_3008_, v_x_47667__boxed_3011_, v_x_3010_);
lean_dec_ref(v_x_3010_);
lean_dec_ref(v_x_3008_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_3014_, uint8_t v_skipAuxDecl_3015_, lean_object* v_auxDeclToFullName_3016_, lean_object* v___x_3017_, lean_object* v_givenNameView_3018_, lean_object* v_as_3019_, lean_object* v_i_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_3014_, v_skipAuxDecl_3015_, v_auxDeclToFullName_3016_, v___x_3017_, v_givenNameView_3018_, v_as_3019_, v_i_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_3023_, lean_object* v_skipAuxDecl_3024_, lean_object* v_auxDeclToFullName_3025_, lean_object* v___x_3026_, lean_object* v_givenNameView_3027_, lean_object* v_as_3028_, lean_object* v_i_3029_, lean_object* v_a_3030_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3031_; lean_object* v_res_3032_; 
v_skipAuxDecl_boxed_3031_ = lean_unbox(v_skipAuxDecl_3024_);
v_res_3032_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_3023_, v_skipAuxDecl_boxed_3031_, v_auxDeclToFullName_3025_, v___x_3026_, v_givenNameView_3027_, v_as_3028_, v_i_3029_, v_a_3030_);
lean_dec_ref(v_as_3028_);
lean_dec(v_auxDeclToFullName_3025_);
lean_dec(v_givenName_3023_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_3033_, lean_object* v_givenName_3034_, lean_object* v_as_3035_, lean_object* v_i_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_3033_, v_givenName_3034_, v_as_3035_, v_i_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3039_, lean_object* v_givenName_3040_, lean_object* v_as_3041_, lean_object* v_i_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3039_, v_givenName_3040_, v_as_3041_, v_i_3042_, v_a_3043_);
lean_dec_ref(v_as_3041_);
lean_dec(v_givenName_3040_);
lean_dec(v_localDecl_x3f_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3045_, lean_object* v_filter_3046_, lean_object* v_view_x3f_3047_, lean_object* v_as_3048_, lean_object* v_as_x27_3049_, lean_object* v_b_3050_, lean_object* v_a_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3045_, v_filter_3046_, v_view_x3f_3047_, v_as_x27_3049_, v_b_3050_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3058_, lean_object* v_filter_3059_, lean_object* v_view_x3f_3060_, lean_object* v_as_3061_, lean_object* v_as_x27_3062_, lean_object* v_b_3063_, lean_object* v_a_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3058_, v_filter_3059_, v_view_x3f_3060_, v_as_3061_, v_as_x27_3062_, v_b_3063_, v_a_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v_as_x27_3062_);
lean_dec(v_as_3061_);
lean_dec(v_n_u2080_3058_);
return v_res_3070_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3071_, lean_object* v_keys_3072_, lean_object* v_vals_3073_, lean_object* v_heq_3074_, lean_object* v_i_3075_, lean_object* v_k_3076_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3072_, v_i_3075_, v_k_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3078_, lean_object* v_keys_3079_, lean_object* v_vals_3080_, lean_object* v_heq_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
_start:
{
uint8_t v_res_3084_; lean_object* v_r_3085_; 
v_res_3084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3078_, v_keys_3079_, v_vals_3080_, v_heq_3081_, v_i_3082_, v_k_3083_);
lean_dec_ref(v_k_3083_);
lean_dec_ref(v_vals_3080_);
lean_dec_ref(v_keys_3079_);
v_r_3085_ = lean_box(v_res_3084_);
return v_r_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3086_, uint8_t v_skipAuxDecl_3087_, lean_object* v_auxDeclToFullName_3088_, lean_object* v___x_3089_, lean_object* v_givenNameView_3090_, lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3086_, v_skipAuxDecl_3087_, v_auxDeclToFullName_3088_, v___x_3089_, v_givenNameView_3090_, v_as_3091_, v_i_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3095_, lean_object* v_skipAuxDecl_3096_, lean_object* v_auxDeclToFullName_3097_, lean_object* v___x_3098_, lean_object* v_givenNameView_3099_, lean_object* v_as_3100_, lean_object* v_i_3101_, lean_object* v_a_3102_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3103_; lean_object* v_res_3104_; 
v_skipAuxDecl_boxed_3103_ = lean_unbox(v_skipAuxDecl_3096_);
v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3095_, v_skipAuxDecl_boxed_3103_, v_auxDeclToFullName_3097_, v___x_3098_, v_givenNameView_3099_, v_as_3100_, v_i_3101_, v_a_3102_);
lean_dec_ref(v_as_3100_);
lean_dec(v_auxDeclToFullName_3097_);
lean_dec(v_givenName_3095_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3105_, lean_object* v_givenName_3106_, lean_object* v_as_3107_, lean_object* v_i_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3105_, v_givenName_3106_, v_as_3107_, v_i_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3111_, lean_object* v_givenName_3112_, lean_object* v_as_3113_, lean_object* v_i_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3111_, v_givenName_3112_, v_as_3113_, v_i_3114_, v_a_3115_);
lean_dec_ref(v_as_3113_);
lean_dec(v_givenName_3112_);
lean_dec(v_localDecl_x3f_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3117_, v___y_3120_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec_ref(v_opt_3124_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3131_, v___y_3134_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v_opt_3138_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3145_, lean_object* v_entry_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_env_3150_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = l_Lean_Linter_deprecatedAttr;
v___x_3152_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3151_, v_env_3150_, v_declName_3145_, v_entry_3146_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_inst_3149_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3162_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3162_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 3);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l_Lean_MessageData_ofFormat(v___x_3158_);
v___x_3160_ = l_Lean_throwError___redArg(v_inst_3147_, v_inst_3148_, v___x_3159_);
return v___x_3160_;
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
lean_dec_ref(v_inst_3148_);
lean_dec_ref(v_inst_3147_);
v_a_3163_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3164_ = l_Lean_setEnv___redArg(v_inst_3149_, v_a_3163_);
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_declName_3168_, lean_object* v_entry_3169_){
_start:
{
lean_object* v_toBind_3170_; lean_object* v_getEnv_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; 
v_toBind_3170_ = lean_ctor_get(v_inst_3165_, 1);
lean_inc(v_toBind_3170_);
v_getEnv_3171_ = lean_ctor_get(v_inst_3166_, 0);
lean_inc(v_getEnv_3171_);
v___f_3172_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3172_, 0, v_declName_3168_);
lean_closure_set(v___f_3172_, 1, v_entry_3169_);
lean_closure_set(v___f_3172_, 2, v_inst_3165_);
lean_closure_set(v___f_3172_, 3, v_inst_3167_);
lean_closure_set(v___f_3172_, 4, v_inst_3166_);
v___x_3173_ = lean_apply_4(v_toBind_3170_, lean_box(0), lean_box(0), v_getEnv_3171_, v___f_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_declName_3178_, lean_object* v_entry_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3175_, v_inst_3176_, v_inst_3177_, v_declName_3178_, v_entry_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3181_, lean_object* v_declName_3182_){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3184_ = l_Lean_Linter_deprecatedAttr;
v___x_3185_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3183_, v___x_3184_, v_env_3181_, v_declName_3182_);
if (lean_obj_tag(v___x_3185_) == 0)
{
uint8_t v___x_3186_; 
v___x_3186_ = 0;
return v___x_3186_;
}
else
{
uint8_t v___x_3187_; 
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = 1;
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3188_, lean_object* v_declName_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Lean_Linter_isDeprecated(v_env_3188_, v_declName_3189_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3192_){
_start:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3193_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3194_ = lean_name_eq(v_x_3192_, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3195_);
lean_dec(v_x_3195_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3199_){
_start:
{
lean_object* v___f_3200_; uint8_t v___x_3201_; 
v___f_3200_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3201_ = l_Lean_MessageData_hasTag(v___f_3200_, v_msg_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3202_){
_start:
{
uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_res_3203_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3202_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3205_, lean_object* v_declName_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3208_ = l_Lean_Linter_deprecatedAttr;
v___x_3209_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3207_, v___x_3208_, v_env_3205_, v_declName_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_box(0);
return v___x_3210_;
}
else
{
lean_object* v_val_3211_; lean_object* v_newName_x3f_3212_; 
v_val_3211_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v___x_3209_, 1);
v_newName_x3f_3212_ = lean_ctor_get(v_val_3211_, 0);
lean_inc(v_newName_x3f_3212_);
lean_dec(v_val_3211_);
return v_newName_x3f_3212_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 0)
{
if (lean_obj_tag(v_x_3214_) == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = 1;
return v___x_3215_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 0;
return v___x_3216_;
}
}
else
{
if (lean_obj_tag(v_x_3214_) == 0)
{
uint8_t v___x_3217_; 
v___x_3217_ = 0;
return v___x_3217_;
}
else
{
lean_object* v_head_3218_; lean_object* v_tail_3219_; lean_object* v_head_3220_; lean_object* v_tail_3221_; uint8_t v___x_3222_; 
v_head_3218_ = lean_ctor_get(v_x_3213_, 0);
v_tail_3219_ = lean_ctor_get(v_x_3213_, 1);
v_head_3220_ = lean_ctor_get(v_x_3214_, 0);
v_tail_3221_ = lean_ctor_get(v_x_3214_, 1);
v___x_3222_ = lean_string_dec_eq(v_head_3218_, v_head_3220_);
if (v___x_3222_ == 0)
{
return v___x_3222_;
}
else
{
v_x_3213_ = v_tail_3219_;
v_x_3214_ = v_tail_3221_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3224_, lean_object* v_x_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3224_, v_x_3225_);
lean_dec(v_x_3225_);
lean_dec(v_x_3224_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3228_, lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 0)
{
if (lean_obj_tag(v_x_3229_) == 0)
{
uint8_t v___x_3230_; 
v___x_3230_ = 1;
return v___x_3230_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = 0;
return v___x_3231_;
}
}
else
{
if (lean_obj_tag(v_x_3229_) == 0)
{
uint8_t v___x_3232_; 
v___x_3232_ = 0;
return v___x_3232_;
}
else
{
lean_object* v_head_3233_; lean_object* v_tail_3234_; lean_object* v_head_3235_; lean_object* v_tail_3236_; uint8_t v___y_3238_; lean_object* v_fst_3240_; lean_object* v_snd_3241_; lean_object* v_fst_3242_; lean_object* v_snd_3243_; uint8_t v___x_3244_; 
v_head_3233_ = lean_ctor_get(v_x_3228_, 0);
v_tail_3234_ = lean_ctor_get(v_x_3228_, 1);
v_head_3235_ = lean_ctor_get(v_x_3229_, 0);
v_tail_3236_ = lean_ctor_get(v_x_3229_, 1);
v_fst_3240_ = lean_ctor_get(v_head_3233_, 0);
v_snd_3241_ = lean_ctor_get(v_head_3233_, 1);
v_fst_3242_ = lean_ctor_get(v_head_3235_, 0);
v_snd_3243_ = lean_ctor_get(v_head_3235_, 1);
v___x_3244_ = lean_name_eq(v_fst_3240_, v_fst_3242_);
if (v___x_3244_ == 0)
{
v___y_3238_ = v___x_3244_;
goto v___jp_3237_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3241_, v_snd_3243_);
v___y_3238_ = v___x_3245_;
goto v___jp_3237_;
}
v___jp_3237_:
{
if (v___y_3238_ == 0)
{
return v___y_3238_;
}
else
{
v_x_3228_ = v_tail_3234_;
v_x_3229_ = v_tail_3236_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3246_, lean_object* v_x_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3246_, v_x_3247_);
lean_dec(v_x_3247_);
lean_dec(v_x_3246_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3253_, lean_object* v_newName_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_ref_3260_; 
v_ref_3260_ = lean_ctor_get(v_a_3257_, 2);
if (lean_obj_tag(v_ref_3260_) == 3)
{
lean_object* v_val_3261_; uint8_t v___x_3262_; 
v_val_3261_ = lean_ctor_get(v_ref_3260_, 2);
v___x_3262_ = l_Lean_Name_hasMacroScopes(v_val_3261_);
if (v___x_3262_ == 0)
{
uint8_t v___x_3263_; lean_object* v___x_3341_; 
v___x_3263_ = 1;
v___x_3341_ = l_Lean_Syntax_getRange_x3f(v_ref_3260_, v___x_3263_);
if (lean_obj_tag(v___x_3341_) == 0)
{
if (v___x_3262_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec(v_newName_3254_);
lean_dec(v_declName_3253_);
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
return v___x_3343_;
}
else
{
goto v___jp_3264_;
}
}
else
{
lean_dec_ref_known(v___x_3341_, 1);
goto v___jp_3264_;
}
v___jp_3264_:
{
lean_object* v___x_3265_; 
lean_inc(v_val_3261_);
v___x_3265_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3261_, v___x_3263_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3332_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3332_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3332_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_declName_3253_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v___x_3270_);
v___x_3273_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3266_, v___x_3272_);
lean_dec_ref_known(v___x_3272_, 2);
lean_dec(v_a_3266_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_newName_3254_);
v___x_3274_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3274_);
v___x_3276_ = v___x_3268_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
else
{
lean_object* v___x_3278_; 
lean_del_object(v___x_3268_);
v___x_3278_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_newName_3254_, v___x_3262_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3323_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3323_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3323_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
if (lean_obj_tag(v_a_3279_) == 1)
{
lean_object* v_val_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3318_; 
lean_del_object(v___x_3281_);
v_val_3283_ = lean_ctor_get(v_a_3279_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3279_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3285_ = v_a_3279_;
v_isShared_3286_ = v_isSharedCheck_3318_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_val_3283_);
lean_dec(v_a_3279_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3318_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3287_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3288_ = l_Lean_Name_toString(v_val_3283_, v___x_3263_);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
lean_ctor_set(v___x_3291_, 2, v___x_3290_);
lean_ctor_set(v___x_3291_, 3, v___x_3290_);
lean_ctor_set(v___x_3291_, 4, v___x_3290_);
lean_ctor_set(v___x_3291_, 5, v___x_3290_);
v___x_3292_ = 0;
v___x_3293_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3290_);
lean_ctor_set(v___x_3293_, 2, v___x_3290_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*3, v___x_3292_);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
v___x_3296_ = lean_array_push(v___x_3295_, v___x_3293_);
lean_inc_ref(v_ref_3260_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v_ref_3260_);
v___x_3298_ = v___x_3285_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_ref_3260_);
v___x_3298_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_MessageData_hint(v___x_3287_, v___x_3296_, v___x_3298_, v___x_3290_, v___x_3262_, v_a_3257_, v_a_3258_);
lean_dec_ref(v___x_3296_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3308_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_a_3300_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3304_);
v___x_3306_ = v___x_3302_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3299_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3299_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
lean_dec(v_a_3279_);
v___x_3319_ = lean_box(0);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3319_);
v___x_3321_ = v___x_3281_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
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
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3278_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3278_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_newName_3254_);
lean_dec(v_declName_3253_);
v_a_3333_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3265_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3265_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v_newName_3254_);
lean_dec(v_declName_3253_);
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v_newName_3254_);
lean_dec(v_declName_3253_);
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3348_, lean_object* v_newName_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3348_, v_newName_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v_env_3360_; lean_object* v___x_3361_; lean_object* v_toEnvExtension_3362_; lean_object* v_asyncMode_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v_merged_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3375_; 
v___x_3359_ = lean_st_ref_get(v___y_3357_);
v_env_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_ref(v_env_3360_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3362_ = lean_ctor_get(v___x_3361_, 0);
v_asyncMode_3363_ = lean_ctor_get(v_toEnvExtension_3362_, 2);
v___x_3364_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3365_ = lean_box(0);
v___x_3366_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3364_, v___x_3361_, v_env_3360_, v_asyncMode_3363_, v___x_3365_);
v_merged_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; 
v_unused_3376_ = lean_ctor_get(v___x_3366_, 1);
lean_dec(v_unused_3376_);
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_merged_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_merged_3367_);
lean_ctor_set(v___x_3369_, 0, v_o_3356_);
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_o_3356_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_merged_3367_);
v___x_3372_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
return v___x_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3377_, v___y_3378_);
lean_dec(v___y_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_toCold_3386_; lean_object* v_options_3387_; lean_object* v___x_3388_; 
v_toCold_3386_ = lean_ctor_get(v___y_3383_, 0);
v_options_3387_ = lean_ctor_get(v_toCold_3386_, 2);
lean_inc_ref(v_options_3387_);
v___x_3388_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_3387_, v___y_3384_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3394_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3397_ = l_Lean_stringToMessageData(v___x_3396_);
return v___x_3397_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3400_ = l_Lean_stringToMessageData(v___x_3399_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3403_ = l_Lean_stringToMessageData(v___x_3402_);
return v___x_3403_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3406_ = l_Lean_stringToMessageData(v___x_3405_);
return v___x_3406_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3409_ = l_Lean_stringToMessageData(v___x_3408_);
return v___x_3409_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3412_ = l_Lean_stringToMessageData(v___x_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3419_ = l_Lean_MessageData_ofFormat(v___x_3418_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3438_, uint8_t v_allowSuggestion_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3618_; 
v___x_3445_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3618_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3618_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; uint8_t v___x_3451_; lean_object* v_extraMsg_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; 
v___x_3450_ = l_Lean_Linter_linter_deprecated;
v___x_3451_ = l_Lean_Linter_getLinterValue(v___x_3450_, v_a_3446_);
lean_dec(v_a_3446_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
lean_dec(v_declName_3438_);
v___x_3467_ = lean_box(0);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3467_);
v___x_3469_ = v___x_3448_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
else
{
lean_object* v___x_3471_; lean_object* v_env_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3471_ = lean_st_ref_get(v_a_3443_);
v_env_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc_ref(v_env_3472_);
lean_dec(v___x_3471_);
v___x_3473_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3474_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3438_);
v___x_3475_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3473_, v___x_3474_, v_env_3472_, v_declName_3438_);
if (lean_obj_tag(v___x_3475_) == 1)
{
lean_object* v_val_3476_; lean_object* v_text_x3f_3477_; 
lean_del_object(v___x_3448_);
v_val_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v_text_x3f_3477_ = lean_ctor_get(v_val_3476_, 1);
if (lean_obj_tag(v_text_x3f_3477_) == 0)
{
lean_object* v_newName_x3f_3478_; 
v_newName_x3f_3478_ = lean_ctor_get(v_val_3476_, 0);
lean_inc(v_newName_x3f_3478_);
lean_dec(v_val_3476_);
if (lean_obj_tag(v_newName_x3f_3478_) == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_3453_ = v___x_3479_;
v___y_3454_ = v_a_3440_;
v___y_3455_ = v_a_3441_;
v___y_3456_ = v_a_3442_;
v___y_3457_ = v_a_3443_;
goto v___jp_3452_;
}
else
{
lean_object* v_val_3480_; lean_object* v___x_3481_; lean_object* v_env_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; 
v_val_3480_ = lean_ctor_get(v_newName_x3f_3478_, 0);
lean_inc_n(v_val_3480_, 2);
lean_dec_ref_known(v_newName_x3f_3478_, 1);
v___x_3481_ = lean_st_ref_get(v_a_3443_);
v_env_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc_ref_n(v_env_3482_, 2);
lean_dec(v___x_3481_);
v___x_3483_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3484_ = l_Lean_MessageData_ofConstName(v_val_3480_, v___x_3451_);
lean_inc_ref(v___x_3484_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_Name_getPrefix(v_declName_3438_);
v___x_3489_ = 0;
lean_inc(v_declName_3438_);
v___x_3490_ = l_Lean_Environment_find_x3f(v_env_3482_, v_declName_3438_, v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_val_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = l_Lean_Name_getPrefix(v_val_3480_);
lean_inc(v_val_3480_);
lean_inc_ref(v_env_3482_);
v___x_3493_ = l_Lean_Environment_find_x3f(v_env_3482_, v_val_3480_, v___x_3489_);
if (lean_obj_tag(v___x_3493_) == 1)
{
lean_object* v_val_3494_; lean_object* v___x_3495_; 
v_val_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_val_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3491_, v_val_3494_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_msg_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___y_3556_; lean_object* v_msg_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___x_3590_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3590_ = lean_unbox(v_a_3496_);
if (v___x_3590_ == 0)
{
if (v___x_3451_ == 0)
{
lean_dec(v_val_3494_);
lean_dec(v_val_3491_);
v_msg_3583_ = v___x_3487_;
v___y_3584_ = v_a_3440_;
v___y_3585_ = v_a_3441_;
v___y_3586_ = v_a_3442_;
v___y_3587_ = v_a_3443_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3591_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3592_ = l_Lean_ConstantInfo_type(v_val_3494_);
lean_dec(v_val_3494_);
v___x_3593_ = l_Lean_indentExpr(v___x_3592_);
v___x_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Lean_ConstantInfo_type(v_val_3491_);
lean_dec(v_val_3491_);
v___x_3598_ = l_Lean_indentExpr(v___x_3597_);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3596_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Lean_MessageData_note(v___x_3599_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3487_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v_msg_3583_ = v___x_3601_;
v___y_3584_ = v_a_3440_;
v___y_3585_ = v_a_3441_;
v___y_3586_ = v_a_3442_;
v___y_3587_ = v_a_3443_;
goto v___jp_3582_;
}
}
else
{
lean_dec(v_val_3494_);
lean_dec(v_val_3491_);
v_msg_3583_ = v___x_3487_;
v___y_3584_ = v_a_3440_;
v___y_3585_ = v_a_3441_;
v___y_3586_ = v_a_3442_;
v___y_3587_ = v_a_3443_;
goto v___jp_3582_;
}
v___jp_3497_:
{
if (v_allowSuggestion_3439_ == 0)
{
lean_dec(v_a_3496_);
lean_dec(v_val_3480_);
v_extraMsg_3453_ = v_msg_3498_;
v___y_3454_ = v___y_3499_;
v___y_3455_ = v___y_3500_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3502_;
goto v___jp_3452_;
}
else
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_unbox(v_a_3496_);
lean_dec(v_a_3496_);
if (v___x_3503_ == 0)
{
lean_dec(v_val_3480_);
v_extraMsg_3453_ = v_msg_3498_;
v___y_3454_ = v___y_3499_;
v___y_3455_ = v___y_3500_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3502_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3504_; 
lean_inc(v_declName_3438_);
v___x_3504_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3438_, v_val_3480_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
if (lean_obj_tag(v_a_3505_) == 1)
{
lean_object* v_val_3506_; lean_object* v___x_3507_; 
v_val_3506_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v_a_3505_, 1);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_msg_3498_);
lean_ctor_set(v___x_3507_, 1, v_val_3506_);
v_extraMsg_3453_ = v___x_3507_;
v___y_3454_ = v___y_3499_;
v___y_3455_ = v___y_3500_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3502_;
goto v___jp_3452_;
}
else
{
lean_dec(v_a_3505_);
v_extraMsg_3453_ = v_msg_3498_;
v___y_3454_ = v___y_3499_;
v___y_3455_ = v___y_3500_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3502_;
goto v___jp_3452_;
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_msg_3498_);
lean_dec(v_declName_3438_);
v_a_3508_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3504_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3504_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
v___jp_3516_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3523_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___x_3484_);
v___x_3525_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___y_3522_);
v___x_3528_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_MessageData_ofName(v___x_3492_);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_MessageData_note(v___x_3533_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___y_3518_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v_msg_3498_ = v___x_3535_;
v___y_3499_ = v___y_3519_;
v___y_3500_ = v___y_3517_;
v___y_3501_ = v___y_3521_;
v___y_3502_ = v___y_3520_;
goto v___jp_3497_;
}
v___jp_3536_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3543_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v___y_3542_);
v___x_3545_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_MessageData_note(v___x_3546_);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___y_3538_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v_msg_3498_ = v___x_3548_;
v___y_3499_ = v___y_3539_;
v___y_3500_ = v___y_3537_;
v___y_3501_ = v___y_3541_;
v___y_3502_ = v___y_3540_;
goto v___jp_3497_;
}
v___jp_3549_:
{
if (v___y_3556_ == 0)
{
uint8_t v___x_3557_; 
lean_inc(v_declName_3438_);
lean_inc_ref(v_env_3482_);
v___x_3557_ = l_Lean_isProtected(v_env_3482_, v_declName_3438_);
if (v___x_3557_ == 0)
{
if (v___x_3451_ == 0)
{
lean_dec(v___x_3492_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
v_msg_3498_ = v___y_3551_;
v___y_3499_ = v___y_3553_;
v___y_3500_ = v___y_3550_;
v___y_3501_ = v___y_3555_;
v___y_3502_ = v___y_3554_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3558_; 
lean_inc(v_val_3480_);
v___x_3558_ = l_Lean_isProtected(v_env_3482_, v_val_3480_);
if (v___x_3558_ == 0)
{
lean_dec(v___x_3492_);
lean_dec_ref(v___x_3484_);
v_msg_3498_ = v___y_3551_;
v___y_3499_ = v___y_3553_;
v___y_3500_ = v___y_3550_;
v___y_3501_ = v___y_3555_;
v___y_3502_ = v___y_3554_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
lean_inc(v___x_3492_);
v___x_3559_ = l_Lean_Name_componentsRev(v___x_3492_);
v___x_3560_ = lean_unsigned_to_nat(1u);
v___x_3561_ = l_List_lengthTR___redArg(v___x_3559_);
v___x_3562_ = lean_nat_dec_lt(v___x_3560_, v___x_3561_);
lean_dec(v___x_3561_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
lean_dec(v___x_3559_);
v___x_3563_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3517_ = v___y_3550_;
v___y_3518_ = v___y_3551_;
v___y_3519_ = v___y_3553_;
v___y_3520_ = v___y_3554_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___x_3563_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3564_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3565_ = lean_unsigned_to_nat(0u);
v___x_3566_ = l_List_get___redArg(v___x_3559_, v___x_3565_);
lean_dec(v___x_3559_);
v___x_3567_ = l_Lean_MessageData_ofName(v___x_3566_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3564_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___y_3517_ = v___y_3550_;
v___y_3518_ = v___y_3551_;
v___y_3519_ = v___y_3553_;
v___y_3520_ = v___y_3554_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___x_3570_;
goto v___jp_3516_;
}
}
}
}
else
{
lean_dec(v___x_3492_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
v_msg_3498_ = v___y_3551_;
v___y_3499_ = v___y_3553_;
v___y_3500_ = v___y_3550_;
v___y_3501_ = v___y_3555_;
v___y_3502_ = v___y_3554_;
goto v___jp_3497_;
}
}
else
{
lean_dec(v___x_3492_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
if (lean_obj_tag(v_declName_3438_) == 1)
{
lean_object* v_str_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_str_3571_ = lean_ctor_get(v_declName_3438_, 1);
v___x_3572_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3571_);
v___x_3573_ = l_Lean_stringToMessageData(v_str_3571_);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
lean_inc(v_val_3480_);
v___x_3577_ = l_Lean_MessageData_ofConstName(v_val_3480_, v___y_3552_);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___y_3537_ = v___y_3550_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3553_;
v___y_3540_ = v___y_3554_;
v___y_3541_ = v___y_3555_;
v___y_3542_ = v___x_3580_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_MessageData_nil;
v___y_3537_ = v___y_3550_;
v___y_3538_ = v___y_3551_;
v___y_3539_ = v___y_3553_;
v___y_3540_ = v___y_3554_;
v___y_3541_ = v___y_3555_;
v___y_3542_ = v___x_3581_;
goto v___jp_3536_;
}
}
}
v___jp_3582_:
{
uint8_t v___x_3588_; 
v___x_3588_ = l_Lean_Name_isAnonymous(v___x_3488_);
if (v___x_3588_ == 0)
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_name_eq(v___x_3488_, v___x_3492_);
lean_dec(v___x_3488_);
if (v___x_3589_ == 0)
{
v___y_3550_ = v___y_3585_;
v___y_3551_ = v_msg_3583_;
v___y_3552_ = v___x_3588_;
v___y_3553_ = v___y_3584_;
v___y_3554_ = v___y_3587_;
v___y_3555_ = v___y_3586_;
v___y_3556_ = v___x_3451_;
goto v___jp_3549_;
}
else
{
v___y_3550_ = v___y_3585_;
v___y_3551_ = v_msg_3583_;
v___y_3552_ = v___x_3588_;
v___y_3553_ = v___y_3584_;
v___y_3554_ = v___y_3587_;
v___y_3555_ = v___y_3586_;
v___y_3556_ = v___x_3588_;
goto v___jp_3549_;
}
}
else
{
lean_dec(v___x_3492_);
lean_dec(v___x_3488_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
v_msg_3498_ = v_msg_3583_;
v___y_3499_ = v___y_3584_;
v___y_3500_ = v___y_3585_;
v___y_3501_ = v___y_3586_;
v___y_3502_ = v___y_3587_;
goto v___jp_3497_;
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_val_3494_);
lean_dec(v___x_3492_);
lean_dec(v_val_3491_);
lean_dec(v___x_3488_);
lean_dec_ref_known(v___x_3487_, 2);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
lean_dec(v_val_3480_);
lean_dec(v_declName_3438_);
v_a_3602_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3495_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3495_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_dec(v___x_3493_);
lean_dec(v___x_3492_);
lean_dec(v_val_3491_);
lean_dec(v___x_3488_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
lean_dec(v_val_3480_);
v_extraMsg_3453_ = v___x_3487_;
v___y_3454_ = v_a_3440_;
v___y_3455_ = v_a_3441_;
v___y_3456_ = v_a_3442_;
v___y_3457_ = v_a_3443_;
goto v___jp_3452_;
}
}
else
{
lean_dec(v___x_3490_);
lean_dec(v___x_3488_);
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_env_3482_);
lean_dec(v_val_3480_);
v_extraMsg_3453_ = v___x_3487_;
v___y_3454_ = v_a_3440_;
v___y_3455_ = v_a_3441_;
v___y_3456_ = v_a_3442_;
v___y_3457_ = v_a_3443_;
goto v___jp_3452_;
}
}
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_inc_ref(v_text_x3f_3477_);
lean_dec(v_val_3476_);
v_val_3610_ = lean_ctor_get(v_text_x3f_3477_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v_text_x3f_3477_, 1);
v___x_3611_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3612_ = l_Lean_stringToMessageData(v_val_3610_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v_extraMsg_3453_ = v___x_3613_;
v___y_3454_ = v_a_3440_;
v___y_3455_ = v_a_3441_;
v___y_3456_ = v_a_3442_;
v___y_3457_ = v_a_3443_;
goto v___jp_3452_;
}
}
else
{
lean_object* v___x_3614_; lean_object* v___x_3616_; 
lean_dec(v___x_3475_);
lean_dec(v_declName_3438_);
v___x_3614_ = lean_box(0);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3614_);
v___x_3616_ = v___x_3448_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
v___jp_3452_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3458_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3459_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3460_ = l_Lean_MessageData_ofConstName(v_declName_3438_, v___x_3451_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_extraMsg_3453_);
v___x_3465_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3458_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_3465_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3619_, lean_object* v_allowSuggestion_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
uint8_t v_allowSuggestion_boxed_3626_; lean_object* v_res_3627_; 
v_allowSuggestion_boxed_3626_ = lean_unbox(v_allowSuggestion_3620_);
v_res_3627_ = l_Lean_Linter_checkDeprecated(v_declName_3619_, v_allowSuggestion_boxed_3626_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3628_, v___y_3632_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
return v_res_3641_;
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
