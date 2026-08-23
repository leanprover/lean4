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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 372, .m_capacity = 372, .m_length = 371, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__12_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__18_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__21_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__23_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__27_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "This warning can be disabled with `set_option "};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "` is itself deprecated, but without an explicit replacement; `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` is being deprecated in favor of a deprecated declaration"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is itself deprecated in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; consider deprecating `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` in favor of `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0_value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0_value)} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Replace the deprecated name:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0 = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1_value)}};
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
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2081_105_);
v___x_113_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2082_106_);
v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
lean_dec(v___x_113_);
lean_dec(v___x_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
else
{
lean_object* v_keyedConfig_117_; uint8_t v_trackZetaDelta_118_; lean_object* v_zetaDeltaSet_119_; lean_object* v_lctx_120_; lean_object* v_localInstances_121_; lean_object* v_defEqCtx_x3f_122_; lean_object* v_synthPendingDepth_123_; lean_object* v_customCanUnfoldPredicate_x3f_124_; uint8_t v_univApprox_125_; uint8_t v_inTypeClassResolution_126_; uint8_t v_cacheInferType_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_levels_130_; lean_object* v_type_u2081_131_; lean_object* v_type_u2082_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_keyedConfig_117_ = lean_ctor_get(v_a_107_, 0);
v_trackZetaDelta_118_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7);
v_zetaDeltaSet_119_ = lean_ctor_get(v_a_107_, 1);
v_lctx_120_ = lean_ctor_get(v_a_107_, 2);
v_localInstances_121_ = lean_ctor_get(v_a_107_, 3);
v_defEqCtx_x3f_122_ = lean_ctor_get(v_a_107_, 4);
v_synthPendingDepth_123_ = lean_ctor_get(v_a_107_, 5);
v_customCanUnfoldPredicate_x3f_124_ = lean_ctor_get(v_a_107_, 6);
v_univApprox_125_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_126_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 2);
v_cacheInferType_127_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 3);
v___x_128_ = l_Lean_ConstantInfo_levelParams(v_decl_u2081_105_);
v___x_129_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_130_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
lean_inc(v_levels_130_);
v_type_u2081_131_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_105_, v_levels_130_);
v_type_u2082_132_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_106_, v_levels_130_);
v___x_133_ = 2;
lean_inc_ref(v_keyedConfig_117_);
v___x_134_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_133_, v_keyedConfig_117_);
lean_inc(v_customCanUnfoldPredicate_x3f_124_);
lean_inc(v_synthPendingDepth_123_);
lean_inc(v_defEqCtx_x3f_122_);
lean_inc_ref(v_localInstances_121_);
lean_inc_ref(v_lctx_120_);
lean_inc(v_zetaDeltaSet_119_);
v___x_135_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_zetaDeltaSet_119_);
lean_ctor_set(v___x_135_, 2, v_lctx_120_);
lean_ctor_set(v___x_135_, 3, v_localInstances_121_);
lean_ctor_set(v___x_135_, 4, v_defEqCtx_x3f_122_);
lean_ctor_set(v___x_135_, 5, v_synthPendingDepth_123_);
lean_ctor_set(v___x_135_, 6, v_customCanUnfoldPredicate_x3f_124_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*7, v_trackZetaDelta_118_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*7 + 1, v_univApprox_125_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*7 + 2, v_inTypeClassResolution_126_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*7 + 3, v_cacheInferType_127_);
v___x_136_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_131_, v_type_u2082_132_, v___x_135_, v_a_108_, v_a_109_, v_a_110_);
lean_dec_ref_known(v___x_135_, 7);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_137_, lean_object* v_decl_u2082_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_137_, v_decl_u2082_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_decl_u2082_138_);
lean_dec_ref(v_decl_u2081_137_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(lean_object* v_opts_145_, lean_object* v_opt_146_){
_start:
{
lean_object* v_name_147_; lean_object* v_defValue_148_; lean_object* v_map_149_; lean_object* v___x_150_; 
v_name_147_ = lean_ctor_get(v_opt_146_, 0);
v_defValue_148_ = lean_ctor_get(v_opt_146_, 1);
v_map_149_ = lean_ctor_get(v_opts_145_, 0);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_149_, v_name_147_);
if (lean_obj_tag(v___x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_defValue_148_);
return v___x_151_;
}
else
{
lean_object* v_val_152_; 
v_val_152_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_150_, 1);
if (lean_obj_tag(v_val_152_) == 1)
{
uint8_t v_v_153_; 
v_v_153_ = lean_ctor_get_uint8(v_val_152_, 0);
lean_dec_ref_known(v_val_152_, 0);
return v_v_153_;
}
else
{
uint8_t v___x_154_; 
lean_dec(v_val_152_);
v___x_154_ = lean_unbox(v_defValue_148_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4___boxed(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_opts_155_, v_opt_156_);
lean_dec_ref(v_opt_156_);
lean_dec_ref(v_opts_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5(lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
if (lean_obj_tag(v_x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
else
{
if (lean_obj_tag(v_x_160_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
lean_object* v_val_164_; lean_object* v_val_165_; uint8_t v___x_166_; 
v_val_164_ = lean_ctor_get(v_x_159_, 0);
v_val_165_ = lean_ctor_get(v_x_160_, 0);
v___x_166_ = lean_name_eq(v_val_164_, v_val_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(uint8_t v___x_171_, lean_object* v_env_172_, lean_object* v_n_173_, lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lean_Environment_contains(v_env_172_, v_n_173_, v___x_171_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object* v___x_176_, lean_object* v_env_177_, lean_object* v_n_178_, lean_object* v_x_179_){
_start:
{
uint8_t v___x_15059__boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v___x_15059__boxed_180_ = lean_unbox(v___x_176_);
v_res_181_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(v___x_15059__boxed_180_, v_env_177_, v_n_178_, v_x_179_);
lean_dec_ref(v_x_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(v_x_186_);
lean_dec_ref(v_x_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(v_x_195_, v_x_196_, v_x_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v_x_197_);
lean_dec_ref(v_x_196_);
lean_dec(v_x_195_);
return v_res_200_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg(lean_object* v_keys_201_, lean_object* v_i_202_, lean_object* v_k_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_array_get_size(v_keys_201_);
v___x_205_ = lean_nat_dec_lt(v_i_202_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_i_202_);
return v___x_205_;
}
else
{
lean_object* v_k_x27_206_; uint8_t v___x_207_; 
v_k_x27_206_ = lean_array_fget_borrowed(v_keys_201_, v_i_202_);
v___x_207_ = l_Lean_instBEqExtraModUse_beq(v_k_203_, v_k_x27_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_i_202_, v___x_208_);
lean_dec(v_i_202_);
v_i_202_ = v___x_209_;
goto _start;
}
else
{
lean_dec(v_i_202_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object* v_keys_211_, lean_object* v_i_212_, lean_object* v_k_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg(v_keys_211_, v_i_212_, v_k_213_);
lean_dec_ref(v_k_213_);
lean_dec_ref(v_keys_211_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg(lean_object* v_x_216_, size_t v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_es_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v_j_223_; lean_object* v___x_224_; 
v_es_219_ = lean_ctor_get(v_x_216_, 0);
v___x_220_ = lean_box(2);
v___x_221_ = ((size_t)31ULL);
v___x_222_ = lean_usize_land(v_x_217_, v___x_221_);
v_j_223_ = lean_usize_to_nat(v___x_222_);
v___x_224_ = lean_array_get_borrowed(v___x_220_, v_es_219_, v_j_223_);
lean_dec(v_j_223_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_key_225_; uint8_t v___x_226_; 
v_key_225_ = lean_ctor_get(v___x_224_, 0);
v___x_226_ = l_Lean_instBEqExtraModUse_beq(v_x_218_, v_key_225_);
return v___x_226_;
}
case 1:
{
lean_object* v_node_227_; size_t v___x_228_; size_t v___x_229_; 
v_node_227_ = lean_ctor_get(v___x_224_, 0);
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_usize_shift_right(v_x_217_, v___x_228_);
v_x_216_ = v_node_227_;
v_x_217_ = v___x_229_;
goto _start;
}
default: 
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
}
else
{
lean_object* v_ks_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_ks_232_ = lean_ctor_get(v_x_216_, 0);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg(v_ks_232_, v___x_233_, v_x_218_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_15107__boxed_238_; uint8_t v_res_239_; lean_object* v_r_240_; 
v_x_15107__boxed_238_ = lean_unbox_usize(v_x_236_);
lean_dec(v_x_236_);
v_res_239_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg(v_x_235_, v_x_15107__boxed_238_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_235_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint64_t v___x_243_; size_t v___x_244_; uint8_t v___x_245_; 
v___x_243_ = l_Lean_instHashableExtraModUse_hash(v_x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg(v_x_241_, v___x_244_, v_x_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_246_, v_x_247_);
lean_dec_ref(v_x_247_);
lean_dec_ref(v_x_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_250_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
lean_ctor_set(v___x_255_, 4, v___x_253_);
lean_ctor_set(v___x_255_, 5, v___x_253_);
lean_ctor_set(v___x_255_, 6, v___x_253_);
lean_ctor_set(v___x_255_, 7, v___x_253_);
lean_ctor_set(v___x_255_, 8, v___x_253_);
lean_ctor_set(v___x_255_, 9, v___x_253_);
lean_ctor_set(v___x_255_, 10, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(32u);
v___x_257_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((size_t)5ULL);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_unsigned_to_nat(32u);
v___x_262_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_264_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_260_);
lean_ctor_set(v___x_264_, 3, v___x_260_);
lean_ctor_set_usize(v___x_264_, 4, v___x_259_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(1);
v___x_266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_env_274_; lean_object* v_options_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_273_ = lean_st_ref_get(v___y_271_);
v_env_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc_ref(v_env_274_);
lean_dec(v___x_273_);
v_options_275_ = lean_ctor_get(v___y_270_, 2);
v___x_276_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_277_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_275_);
v___x_278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_278_, 0, v_env_274_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_277_);
lean_ctor_set(v___x_278_, 3, v_options_275_);
v___x_279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_msgData_269_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(v_msgData_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_285_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_286_; double v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_float_of_nat(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_291_, lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_ref_296_; lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_342_; 
v_ref_296_ = lean_ctor_get(v___y_293_, 5);
v___x_297_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(v_msg_292_, v___y_293_, v___y_294_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_342_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_342_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_342_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_341_; 
v___x_302_ = lean_st_ref_take(v___y_294_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
v_env_304_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_305_ = lean_ctor_get(v___x_302_, 1);
v_ngen_306_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_307_ = lean_ctor_get(v___x_302_, 3);
v_cache_308_ = lean_ctor_get(v___x_302_, 5);
v_messages_309_ = lean_ctor_get(v___x_302_, 6);
v_infoState_310_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_311_ = lean_ctor_get(v___x_302_, 8);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_341_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_341_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snapshotTasks_311_);
lean_inc(v_infoState_310_);
lean_inc(v_messages_309_);
lean_inc(v_cache_308_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_307_);
lean_inc(v_ngen_306_);
lean_inc(v_nextMacroScope_305_);
lean_inc(v_env_304_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_341_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v_traces_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_340_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_traces_316_ = lean_ctor_get(v_traceState_303_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_340_ == 0)
{
v___x_318_ = v_traceState_303_;
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_traces_316_);
lean_dec(v_traceState_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; double v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_320_ = lean_box(0);
v___x_321_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_322_ = 0;
v___x_323_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_324_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_324_, 0, v_cls_291_);
lean_ctor_set(v___x_324_, 1, v___x_320_);
lean_ctor_set(v___x_324_, 2, v___x_323_);
lean_ctor_set_float(v___x_324_, sizeof(void*)*3, v___x_321_);
lean_ctor_set_float(v___x_324_, sizeof(void*)*3 + 8, v___x_321_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*3 + 16, v___x_322_);
v___x_325_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__2));
v___x_326_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v_a_298_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
lean_inc(v_ref_296_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_ref_296_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_PersistentArray_push___redArg(v_traces_316_, v___x_327_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_328_);
v___x_330_ = v___x_318_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_328_);
lean_ctor_set_uint64(v_reuseFailAlloc_339_, sizeof(void*)*1, v_tid_315_);
v___x_330_ = v_reuseFailAlloc_339_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_330_);
v___x_332_ = v___x_313_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v_snapshotTasks_311_);
v___x_332_ = v_reuseFailAlloc_338_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = lean_st_ref_put(v___y_294_, v___x_332_);
v___x_334_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_334_);
v___x_336_ = v___x_300_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_343_, v_msg_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_352_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_353_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_352_, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_354_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15(void){
_start:
{
lean_object* v_cls_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_cls_373_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_374_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__14));
v___x_375_ = l_Lean_Name_append(v___x_374_, v_cls_373_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__16));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__18));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_386_, uint8_t v_isMeta_387_, lean_object* v_hint_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v_env_393_; uint8_t v_isExporting_394_; lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v___x_397_; lean_object* v_entry_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___y_403_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_392_ = lean_st_ref_get(v___y_390_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v_isExporting_394_ = lean_ctor_get_uint8(v_env_393_, sizeof(void*)*8);
lean_dec_ref(v_env_393_);
v___x_395_ = lean_st_ref_get(v___y_390_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v___x_397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_386_);
v_entry_398_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_398_, 0, v_mod_386_);
lean_ctor_set_uint8(v_entry_398_, sizeof(void*)*1, v_isExporting_394_);
lean_ctor_set_uint8(v_entry_398_, sizeof(void*)*1 + 1, v_isMeta_387_);
v___x_399_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_400_ = lean_box(1);
v___x_401_ = lean_box(0);
v___x_428_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_397_, v___x_399_, v_env_396_, v___x_400_, v___x_401_);
v___x_429_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_428_, v_entry_398_);
lean_dec(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v_options_430_; uint8_t v_hasTrace_431_; 
v_options_430_ = lean_ctor_get(v___y_389_, 2);
v_hasTrace_431_ = lean_ctor_get_uint8(v_options_430_, sizeof(void*)*1);
if (v_hasTrace_431_ == 0)
{
lean_dec(v_hint_388_);
lean_dec(v_mod_386_);
v___y_403_ = v___y_390_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_432_; lean_object* v_cls_433_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_inheritedTraceOptions_432_ = lean_ctor_get(v___y_389_, 13);
v_cls_433_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_453_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__15);
v___x_454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_432_, v_options_430_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec(v_hint_388_);
lean_dec(v_mod_386_);
v___y_403_ = v___y_390_;
goto v___jp_402_;
}
else
{
lean_object* v___x_455_; lean_object* v___y_457_; 
v___x_455_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__17);
if (v_isExporting_394_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__22));
v___y_457_ = v___x_464_;
goto v___jp_456_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__23));
v___y_457_ = v___x_465_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref(v___y_457_);
v___x_458_ = l_Lean_stringToMessageData(v___y_457_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_455_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__19);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
if (v_isMeta_387_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__20));
v___y_440_ = v___x_461_;
v___y_441_ = v___x_462_;
goto v___jp_439_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_440_ = v___x_461_;
v___y_441_ = v___x_463_;
goto v___jp_439_;
}
}
}
v___jp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___y_435_);
lean_ctor_set(v___x_437_, 1, v___y_436_);
v___x_438_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_433_, v___x_437_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_dec_ref_known(v___x_438_, 1);
v___y_403_ = v___y_390_;
goto v___jp_402_;
}
else
{
lean_dec_ref_known(v_entry_398_, 1);
return v___x_438_;
}
}
v___jp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
lean_inc_ref(v___y_441_);
v___x_442_ = l_Lean_stringToMessageData(v___y_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___y_440_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_MessageData_ofName(v_mod_386_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_Name_isAnonymous(v_hint_388_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_450_ = l_Lean_MessageData_ofName(v_hint_388_);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___y_435_ = v___x_447_;
v___y_436_ = v___x_451_;
goto v___jp_434_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v_hint_388_);
v___x_452_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___y_435_ = v___x_447_;
v___y_436_ = v___x_452_;
goto v___jp_434_;
}
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref_known(v_entry_398_, 1);
lean_dec(v_hint_388_);
lean_dec(v_mod_386_);
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toEnvExtension_405_; lean_object* v_env_406_; lean_object* v_nextMacroScope_407_; lean_object* v_ngen_408_; lean_object* v_auxDeclNGen_409_; lean_object* v_traceState_410_; lean_object* v_messages_411_; lean_object* v_infoState_412_; lean_object* v_snapshotTasks_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_426_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toEnvExtension_405_ = lean_ctor_get(v___x_399_, 0);
v_env_406_ = lean_ctor_get(v___x_404_, 0);
v_nextMacroScope_407_ = lean_ctor_get(v___x_404_, 1);
v_ngen_408_ = lean_ctor_get(v___x_404_, 2);
v_auxDeclNGen_409_ = lean_ctor_get(v___x_404_, 3);
v_traceState_410_ = lean_ctor_get(v___x_404_, 4);
v_messages_411_ = lean_ctor_get(v___x_404_, 6);
v_infoState_412_ = lean_ctor_get(v___x_404_, 7);
v_snapshotTasks_413_ = lean_ctor_get(v___x_404_, 8);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v___x_404_, 5);
lean_dec(v_unused_427_);
v___x_415_ = v___x_404_;
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snapshotTasks_413_);
lean_inc(v_infoState_412_);
lean_inc(v_messages_411_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_409_);
lean_inc(v_ngen_408_);
lean_inc(v_nextMacroScope_407_);
lean_inc(v_env_406_);
lean_dec(v___x_404_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_asyncMode_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v_asyncMode_417_ = lean_ctor_get(v_toEnvExtension_405_, 2);
v___x_418_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_399_, v_env_406_, v_entry_398_, v_asyncMode_417_, v___x_401_);
v___x_419_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__5);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 5, v___x_419_);
lean_ctor_set(v___x_415_, 0, v___x_418_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_nextMacroScope_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_ngen_408_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_auxDeclNGen_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_traceState_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_messages_411_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_infoState_412_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v_snapshotTasks_413_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_st_ref_put(v___y_403_, v___x_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_468_, lean_object* v_isMeta_469_, lean_object* v_hint_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v_isMeta_boxed_474_; lean_object* v_res_475_; 
v_isMeta_boxed_474_ = lean_unbox(v_isMeta_469_);
v_res_475_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4(v_mod_468_, v_isMeta_boxed_474_, v_hint_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_476_, lean_object* v_declName_477_, lean_object* v_as_478_, size_t v_sz_479_, size_t v_i_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v_declName_477_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_481_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v_modules_488_; lean_object* v___x_489_; lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v_toImport_492_; lean_object* v_module_493_; uint8_t v___x_494_; lean_object* v___x_495_; 
v___x_487_ = l_Lean_Environment_header(v___x_476_);
v_modules_488_ = lean_ctor_get(v___x_487_, 3);
lean_inc_ref(v_modules_488_);
lean_dec_ref(v___x_487_);
v___x_489_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_490_ = lean_array_uget_borrowed(v_as_478_, v_i_480_);
v___x_491_ = lean_array_get(v___x_489_, v_modules_488_, v_a_490_);
lean_dec_ref(v_modules_488_);
v_toImport_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc_ref(v_toImport_492_);
lean_dec(v___x_491_);
v_module_493_ = lean_ctor_get(v_toImport_492_, 0);
lean_inc(v_module_493_);
lean_dec_ref(v_toImport_492_);
v___x_494_ = 0;
lean_inc(v_declName_477_);
v___x_495_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4(v_module_493_, v___x_494_, v_declName_477_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; 
lean_dec_ref_known(v___x_495_, 1);
v___x_496_ = lean_box(0);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_480_, v___x_497_);
v_i_480_ = v___x_498_;
v_b_481_ = v___x_496_;
goto _start;
}
else
{
lean_dec(v_declName_477_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_500_, lean_object* v_declName_501_, lean_object* v_as_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
size_t v_sz_boxed_509_; size_t v_i_boxed_510_; lean_object* v_res_511_; 
v_sz_boxed_509_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_510_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5(v___x_500_, v_declName_501_, v_as_502_, v_sz_boxed_509_, v_i_boxed_510_, v_b_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_as_502_);
lean_dec_ref(v___x_500_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v_key_515_; lean_object* v_value_516_; lean_object* v_tail_517_; uint8_t v___x_518_; 
v_key_515_ = lean_ctor_get(v_x_513_, 0);
v_value_516_ = lean_ctor_get(v_x_513_, 1);
v_tail_517_ = lean_ctor_get(v_x_513_, 2);
v___x_518_ = lean_name_eq(v_key_515_, v_a_512_);
if (v___x_518_ == 0)
{
v_x_513_ = v_tail_517_;
goto _start;
}
else
{
lean_object* v___x_520_; 
lean_inc(v_value_516_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_value_516_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_521_, v_x_522_);
lean_dec(v_x_522_);
lean_dec(v_a_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_buckets_526_; lean_object* v___x_527_; uint64_t v___y_529_; 
v_buckets_526_ = lean_ctor_get(v_m_524_, 1);
v___x_527_ = lean_array_get_size(v_buckets_526_);
if (lean_obj_tag(v_a_525_) == 0)
{
uint64_t v___x_543_; 
v___x_543_ = 1723ULL;
v___y_529_ = v___x_543_;
goto v___jp_528_;
}
else
{
uint64_t v_hash_544_; 
v_hash_544_ = lean_ctor_get_uint64(v_a_525_, sizeof(void*)*2);
v___y_529_ = v_hash_544_;
goto v___jp_528_;
}
v___jp_528_:
{
uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v_fold_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_530_ = 32ULL;
v___x_531_ = lean_uint64_shift_right(v___y_529_, v___x_530_);
v_fold_532_ = lean_uint64_xor(v___y_529_, v___x_531_);
v___x_533_ = 16ULL;
v___x_534_ = lean_uint64_shift_right(v_fold_532_, v___x_533_);
v___x_535_ = lean_uint64_xor(v_fold_532_, v___x_534_);
v___x_536_ = lean_uint64_to_usize(v___x_535_);
v___x_537_ = lean_usize_of_nat(v___x_527_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_sub(v___x_537_, v___x_538_);
v___x_540_ = lean_usize_land(v___x_536_, v___x_539_);
v___x_541_ = lean_array_uget_borrowed(v_buckets_526_, v___x_540_);
v___x_542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_525_, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_m_545_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__1));
v___x_551_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__0));
v___x_552_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_551_, v___x_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2(lean_object* v_declName_555_, uint8_t v_isMeta_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; lean_object* v_env_564_; lean_object* v___y_566_; lean_object* v___x_579_; 
v___x_560_ = lean_st_ref_get(v___y_558_);
v_env_564_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_560_);
v___x_579_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_564_, v_declName_555_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_dec_ref(v_env_564_);
lean_dec(v_declName_555_);
goto v___jp_561_;
}
else
{
lean_object* v_val_580_; lean_object* v___x_581_; lean_object* v_modules_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = l_Lean_Environment_header(v_env_564_);
v_modules_582_ = lean_ctor_get(v___x_581_, 3);
lean_inc_ref(v_modules_582_);
lean_dec_ref(v___x_581_);
v___x_583_ = lean_array_get_size(v_modules_582_);
v___x_584_ = lean_nat_dec_lt(v_val_580_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec_ref(v_modules_582_);
lean_dec(v_val_580_);
lean_dec_ref(v_env_564_);
lean_dec(v_declName_555_);
goto v___jp_561_;
}
else
{
lean_object* v___x_585_; lean_object* v_env_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___y_590_; 
v___x_585_ = lean_st_ref_get(v___y_558_);
v_env_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_585_);
v___x_587_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__2);
v___x_588_ = lean_array_fget(v_modules_582_, v_val_580_);
lean_dec(v_val_580_);
lean_dec_ref(v_modules_582_);
if (v_isMeta_556_ == 0)
{
lean_dec_ref(v_env_586_);
v___y_590_ = v_isMeta_556_;
goto v___jp_589_;
}
else
{
uint8_t v___x_601_; 
lean_inc(v_declName_555_);
v___x_601_ = l_Lean_isMarkedMeta(v_env_586_, v_declName_555_);
if (v___x_601_ == 0)
{
v___y_590_ = v_isMeta_556_;
goto v___jp_589_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = 0;
v___y_590_ = v___x_602_;
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v_toImport_591_; lean_object* v_module_592_; lean_object* v___x_593_; 
v_toImport_591_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_toImport_591_);
lean_dec(v___x_588_);
v_module_592_ = lean_ctor_get(v_toImport_591_, 0);
lean_inc(v_module_592_);
lean_dec_ref(v_toImport_591_);
lean_inc(v_declName_555_);
v___x_593_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4(v_module_592_, v___y_590_, v_declName_555_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_594_ = l_Lean_indirectModUseExt;
v___x_595_ = lean_box(1);
v___x_596_ = lean_box(0);
lean_inc_ref(v_env_564_);
v___x_597_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_587_, v___x_594_, v_env_564_, v___x_595_, v___x_596_);
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_597_, v_declName_555_);
lean_dec(v___x_597_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___closed__3));
v___y_566_ = v___x_599_;
goto v___jp_565_;
}
else
{
lean_object* v_val_600_; 
v_val_600_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v___x_598_, 1);
v___y_566_ = v_val_600_;
goto v___jp_565_;
}
}
else
{
lean_dec_ref(v_env_564_);
lean_dec(v_declName_555_);
return v___x_593_;
}
}
}
}
v___jp_561_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
v___jp_565_:
{
lean_object* v___x_567_; size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_box(0);
v_sz_568_ = lean_array_size(v___y_566_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__5(v_env_564_, v_declName_555_, v___y_566_, v_sz_568_, v___x_569_, v___x_567_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_env_564_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_578_);
v___x_572_ = v___x_570_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_dec(v___x_570_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_567_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_567_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_603_, lean_object* v_isMeta_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v_isMeta_boxed_608_; lean_object* v_res_609_; 
v_isMeta_boxed_608_ = lean_unbox(v_isMeta_604_);
v_res_609_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2(v_declName_603_, v_isMeta_boxed_608_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; lean_object* v_env_614_; lean_object* v___x_615_; lean_object* v_toEnvExtension_616_; lean_object* v_asyncMode_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_merged_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v___x_613_ = lean_st_ref_get(v___y_611_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
v___x_615_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_616_ = lean_ctor_get(v___x_615_, 0);
v_asyncMode_617_ = lean_ctor_get(v_toEnvExtension_616_, 2);
v___x_618_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_619_ = lean_box(0);
v___x_620_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_618_, v___x_615_, v_env_614_, v_asyncMode_617_, v___x_619_);
v_merged_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_620_, 1);
lean_dec(v_unused_630_);
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_merged_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_merged_621_);
lean_ctor_set(v___x_623_, 0, v_o_610_);
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_o_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_merged_621_);
v___x_626_ = v_reuseFailAlloc_628_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_631_, v___y_632_);
lean_dec(v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3(lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_options_638_; lean_object* v___x_639_; 
v_options_638_ = lean_ctor_get(v___y_635_, 2);
lean_inc_ref(v_options_638_);
v___x_639_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg(v_options_638_, v___y_636_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3(v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_ref_648_; lean_object* v___x_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_ref_648_ = lean_ctor_get(v___y_645_, 5);
v___x_649_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(v_msg_644_, v___y_645_, v___y_646_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc(v_ref_648_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v_ref_648_);
lean_ctor_set(v___x_654_, 1, v_a_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 1);
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v_msg_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_671_, uint8_t v___y_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_673_) == 1)
{
lean_object* v_pre_674_; 
v_pre_674_ = lean_ctor_get(v_x_673_, 0);
switch(lean_obj_tag(v_pre_674_))
{
case 1:
{
lean_object* v_pre_675_; 
v_pre_675_ = lean_ctor_get(v_pre_674_, 0);
switch(lean_obj_tag(v_pre_675_))
{
case 0:
{
lean_object* v_str_676_; lean_object* v_str_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_str_676_ = lean_ctor_get(v_x_673_, 1);
v_str_677_ = lean_ctor_get(v_pre_674_, 1);
v___x_678_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_679_ = lean_string_dec_eq(v_str_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_681_ = lean_string_dec_eq(v_str_677_, v___x_680_);
if (v___x_681_ == 0)
{
return v___x_681_;
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_683_ = lean_string_dec_eq(v_str_676_, v___x_682_);
if (v___x_683_ == 0)
{
return v___x_683_;
}
else
{
return v_suppressElabErrors_671_;
}
}
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_685_ = lean_string_dec_eq(v_str_676_, v___x_684_);
if (v___x_685_ == 0)
{
return v___x_685_;
}
else
{
return v_suppressElabErrors_671_;
}
}
}
case 1:
{
lean_object* v_pre_686_; 
v_pre_686_ = lean_ctor_get(v_pre_675_, 0);
if (lean_obj_tag(v_pre_686_) == 0)
{
lean_object* v_str_687_; lean_object* v_str_688_; lean_object* v_str_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_str_687_ = lean_ctor_get(v_x_673_, 1);
v_str_688_ = lean_ctor_get(v_pre_674_, 1);
v_str_689_ = lean_ctor_get(v_pre_675_, 1);
v___x_690_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_691_ = lean_string_dec_eq(v_str_689_, v___x_690_);
if (v___x_691_ == 0)
{
return v___x_691_;
}
else
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_693_ = lean_string_dec_eq(v_str_688_, v___x_692_);
if (v___x_693_ == 0)
{
return v___x_693_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_695_ = lean_string_dec_eq(v_str_687_, v___x_694_);
if (v___x_695_ == 0)
{
return v___x_695_;
}
else
{
return v_suppressElabErrors_671_;
}
}
}
}
else
{
return v___y_672_;
}
}
default: 
{
return v___y_672_;
}
}
}
case 0:
{
lean_object* v_str_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_str_696_ = lean_ctor_get(v_x_673_, 1);
v___x_697_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_698_ = lean_string_dec_eq(v_str_696_, v___x_697_);
if (v___x_698_ == 0)
{
return v___x_698_;
}
else
{
return v_suppressElabErrors_671_;
}
}
default: 
{
return v___y_672_;
}
}
}
else
{
return v___y_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_699_, lean_object* v___y_700_, lean_object* v_x_701_){
_start:
{
uint8_t v_suppressElabErrors_boxed_702_; uint8_t v___y_15881__boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_suppressElabErrors_boxed_702_ = lean_unbox(v_suppressElabErrors_699_);
v___y_15881__boxed_703_ = lean_unbox(v___y_700_);
v_res_704_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_702_, v___y_15881__boxed_703_, v_x_701_);
lean_dec(v_x_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_706_, lean_object* v_msgData_707_, uint8_t v_severity_708_, uint8_t v_isSilent_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; uint8_t v___y_780_; uint8_t v___y_781_; lean_object* v___y_782_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; uint8_t v___y_791_; uint8_t v___y_792_; uint8_t v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; uint8_t v___y_807_; uint8_t v___x_822_; 
v___x_797_ = 2;
v___x_822_ = l_Lean_instBEqMessageSeverity_beq(v_severity_708_, v___x_797_);
if (v___x_822_ == 0)
{
v___y_807_ = v___x_822_;
goto v___jp_806_;
}
else
{
uint8_t v___x_823_; 
lean_inc_ref(v_msgData_707_);
v___x_823_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_707_);
v___y_807_ = v___x_823_;
goto v___jp_806_;
}
v___jp_713_:
{
lean_object* v___x_723_; lean_object* v_currNamespace_724_; lean_object* v_openDecls_725_; lean_object* v_env_726_; lean_object* v_nextMacroScope_727_; lean_object* v_ngen_728_; lean_object* v_auxDeclNGen_729_; lean_object* v_traceState_730_; lean_object* v_cache_731_; lean_object* v_messages_732_; lean_object* v_infoState_733_; lean_object* v_snapshotTasks_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_748_; 
v___x_723_ = lean_st_ref_take(v___y_722_);
v_currNamespace_724_ = lean_ctor_get(v___y_721_, 6);
v_openDecls_725_ = lean_ctor_get(v___y_721_, 7);
v_env_726_ = lean_ctor_get(v___x_723_, 0);
v_nextMacroScope_727_ = lean_ctor_get(v___x_723_, 1);
v_ngen_728_ = lean_ctor_get(v___x_723_, 2);
v_auxDeclNGen_729_ = lean_ctor_get(v___x_723_, 3);
v_traceState_730_ = lean_ctor_get(v___x_723_, 4);
v_cache_731_ = lean_ctor_get(v___x_723_, 5);
v_messages_732_ = lean_ctor_get(v___x_723_, 6);
v_infoState_733_ = lean_ctor_get(v___x_723_, 7);
v_snapshotTasks_734_ = lean_ctor_get(v___x_723_, 8);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_748_ == 0)
{
v___x_736_ = v___x_723_;
v_isShared_737_ = v_isSharedCheck_748_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snapshotTasks_734_);
lean_inc(v_infoState_733_);
lean_inc(v_messages_732_);
lean_inc(v_cache_731_);
lean_inc(v_traceState_730_);
lean_inc(v_auxDeclNGen_729_);
lean_inc(v_ngen_728_);
lean_inc(v_nextMacroScope_727_);
lean_inc(v_env_726_);
lean_dec(v___x_723_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_748_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc(v_openDecls_725_);
lean_inc(v_currNamespace_724_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_currNamespace_724_);
lean_ctor_set(v___x_738_, 1, v_openDecls_725_);
v___x_739_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___y_714_);
lean_inc_ref(v___y_718_);
lean_inc_ref(v___y_716_);
v___x_740_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_740_, 0, v___y_716_);
lean_ctor_set(v___x_740_, 1, v___y_719_);
lean_ctor_set(v___x_740_, 2, v___y_715_);
lean_ctor_set(v___x_740_, 3, v___y_718_);
lean_ctor_set(v___x_740_, 4, v___x_739_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*5, v___y_720_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*5 + 1, v___y_717_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*5 + 2, v_isSilent_709_);
v___x_741_ = l_Lean_MessageLog_add(v___x_740_, v_messages_732_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 6, v___x_741_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_env_726_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_nextMacroScope_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_ngen_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_auxDeclNGen_729_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_traceState_730_);
lean_ctor_set(v_reuseFailAlloc_747_, 5, v_cache_731_);
lean_ctor_set(v_reuseFailAlloc_747_, 6, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 7, v_infoState_733_);
lean_ctor_set(v_reuseFailAlloc_747_, 8, v_snapshotTasks_734_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_st_ref_put(v___y_722_, v___x_743_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
v___jp_749_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_773_; 
v___x_758_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_707_);
v___x_759_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0(v___x_758_, v___y_710_, v___y_711_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_773_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_773_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_773_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_inc_ref_n(v___y_752_, 2);
v___x_764_ = l_Lean_FileMap_toPosition(v___y_752_, v___y_755_);
lean_dec(v___y_755_);
v___x_765_ = l_Lean_FileMap_toPosition(v___y_752_, v___y_757_);
lean_dec(v___y_757_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_754_ == 0)
{
lean_del_object(v___x_762_);
lean_dec_ref(v___y_750_);
v___y_714_ = v_a_760_;
v___y_715_ = v___x_766_;
v___y_716_ = v___y_751_;
v___y_717_ = v___y_753_;
v___y_718_ = v___x_767_;
v___y_719_ = v___x_764_;
v___y_720_ = v___y_756_;
v___y_721_ = v___y_710_;
v___y_722_ = v___y_711_;
goto v___jp_713_;
}
else
{
uint8_t v___x_768_; 
lean_inc(v_a_760_);
v___x_768_ = l_Lean_MessageData_hasTag(v___y_750_, v_a_760_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec_ref_known(v___x_766_, 1);
lean_dec_ref(v___x_764_);
lean_dec(v_a_760_);
v___x_769_ = lean_box(0);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_769_);
v___x_771_ = v___x_762_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_del_object(v___x_762_);
v___y_714_ = v_a_760_;
v___y_715_ = v___x_766_;
v___y_716_ = v___y_751_;
v___y_717_ = v___y_753_;
v___y_718_ = v___x_767_;
v___y_719_ = v___x_764_;
v___y_720_ = v___y_756_;
v___y_721_ = v___y_710_;
v___y_722_ = v___y_711_;
goto v___jp_713_;
}
}
}
}
v___jp_774_:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Syntax_getTailPos_x3f(v___y_776_, v___y_781_);
lean_dec(v___y_776_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_inc(v___y_782_);
v___y_750_ = v___y_775_;
v___y_751_ = v___y_778_;
v___y_752_ = v___y_777_;
v___y_753_ = v___y_779_;
v___y_754_ = v___y_780_;
v___y_755_ = v___y_782_;
v___y_756_ = v___y_781_;
v___y_757_ = v___y_782_;
goto v___jp_749_;
}
else
{
lean_object* v_val_784_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
v___y_750_ = v___y_775_;
v___y_751_ = v___y_778_;
v___y_752_ = v___y_777_;
v___y_753_ = v___y_779_;
v___y_754_ = v___y_780_;
v___y_755_ = v___y_782_;
v___y_756_ = v___y_781_;
v___y_757_ = v_val_784_;
goto v___jp_749_;
}
}
v___jp_785_:
{
lean_object* v_ref_793_; lean_object* v___x_794_; 
v_ref_793_ = l_Lean_replaceRef(v_ref_706_, v___y_787_);
v___x_794_ = l_Lean_Syntax_getPos_x3f(v_ref_793_, v___y_791_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___y_775_ = v___y_786_;
v___y_776_ = v_ref_793_;
v___y_777_ = v___y_789_;
v___y_778_ = v___y_788_;
v___y_779_ = v___y_792_;
v___y_780_ = v___y_790_;
v___y_781_ = v___y_791_;
v___y_782_ = v___x_795_;
goto v___jp_774_;
}
else
{
lean_object* v_val_796_; 
v_val_796_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v___x_794_, 1);
v___y_775_ = v___y_786_;
v___y_776_ = v_ref_793_;
v___y_777_ = v___y_789_;
v___y_778_ = v___y_788_;
v___y_779_ = v___y_792_;
v___y_780_ = v___y_790_;
v___y_781_ = v___y_791_;
v___y_782_ = v_val_796_;
goto v___jp_774_;
}
}
v___jp_798_:
{
if (v___y_805_ == 0)
{
v___y_786_ = v___y_802_;
v___y_787_ = v___y_799_;
v___y_788_ = v___y_801_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_803_;
v___y_791_ = v___y_804_;
v___y_792_ = v_severity_708_;
goto v___jp_785_;
}
else
{
v___y_786_ = v___y_802_;
v___y_787_ = v___y_799_;
v___y_788_ = v___y_801_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_803_;
v___y_791_ = v___y_804_;
v___y_792_ = v___x_797_;
goto v___jp_785_;
}
}
v___jp_806_:
{
if (v___y_807_ == 0)
{
lean_object* v_fileName_808_; lean_object* v_fileMap_809_; lean_object* v_options_810_; lean_object* v_ref_811_; uint8_t v_suppressElabErrors_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___f_815_; uint8_t v___x_816_; uint8_t v___x_817_; 
v_fileName_808_ = lean_ctor_get(v___y_710_, 0);
v_fileMap_809_ = lean_ctor_get(v___y_710_, 1);
v_options_810_ = lean_ctor_get(v___y_710_, 2);
v_ref_811_ = lean_ctor_get(v___y_710_, 5);
v_suppressElabErrors_812_ = lean_ctor_get_uint8(v___y_710_, sizeof(void*)*14 + 1);
v___x_813_ = lean_box(v_suppressElabErrors_812_);
v___x_814_ = lean_box(v___y_807_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_815_, 0, v___x_813_);
lean_closure_set(v___f_815_, 1, v___x_814_);
v___x_816_ = 1;
v___x_817_ = l_Lean_instBEqMessageSeverity_beq(v_severity_708_, v___x_816_);
if (v___x_817_ == 0)
{
v___y_799_ = v_ref_811_;
v___y_800_ = v_fileMap_809_;
v___y_801_ = v_fileName_808_;
v___y_802_ = v___f_815_;
v___y_803_ = v_suppressElabErrors_812_;
v___y_804_ = v___y_807_;
v___y_805_ = v___x_817_;
goto v___jp_798_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = l_Lean_warningAsError;
v___x_819_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_810_, v___x_818_);
v___y_799_ = v_ref_811_;
v___y_800_ = v_fileMap_809_;
v___y_801_ = v_fileName_808_;
v___y_802_ = v___f_815_;
v___y_803_ = v_suppressElabErrors_812_;
v___y_804_ = v___y_807_;
v___y_805_ = v___x_819_;
goto v___jp_798_;
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v_msgData_707_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_824_, lean_object* v_msgData_825_, lean_object* v_severity_826_, lean_object* v_isSilent_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v_severity_boxed_831_; uint8_t v_isSilent_boxed_832_; lean_object* v_res_833_; 
v_severity_boxed_831_ = lean_unbox(v_severity_826_);
v_isSilent_boxed_832_ = lean_unbox(v_isSilent_827_);
v_res_833_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_824_, v_msgData_825_, v_severity_boxed_831_, v_isSilent_boxed_832_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_ref_824_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_834_, uint8_t v_severity_835_, uint8_t v_isSilent_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_ref_840_; lean_object* v___x_841_; 
v_ref_840_ = lean_ctor_get(v___y_837_, 5);
v___x_841_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_840_, v_msgData_834_, v_severity_835_, v_isSilent_836_, v___y_837_, v___y_838_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_842_, lean_object* v_severity_843_, lean_object* v_isSilent_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v_severity_boxed_848_; uint8_t v_isSilent_boxed_849_; lean_object* v_res_850_; 
v_severity_boxed_848_ = lean_unbox(v_severity_843_);
v_isSilent_boxed_849_ = lean_unbox(v_isSilent_844_);
v_res_850_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2(v_msgData_842_, v_severity_boxed_848_, v_isSilent_boxed_849_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(lean_object* v_msgData_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = 1;
v___x_856_ = 0;
v___x_857_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2(v_msgData_851_, v___x_855_, v___x_856_, v___y_852_, v___y_853_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v_msgData_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_862_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_867_ = l_Lean_MessageData_ofFormat(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_872_ = l_Lean_MessageData_ofFormat(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__6_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__8_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__10_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__13_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_886_ = l_Lean_MessageData_ofFormat(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__14_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_888_ = l_Lean_MessageData_hint_x27(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__16_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__19_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_896_ = l_Lean_MessageData_ofFormat(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__24_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_904_ = l_Lean_MessageData_ofFormat(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__25_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__28_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_911_ = l_Lean_MessageData_ofFormat(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_box(1);
v___x_916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_917_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
lean_ctor_set(v___x_918_, 2, v___x_915_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set(v___x_923_, 3, v___x_922_);
lean_ctor_set(v___x_923_, 4, v___x_921_);
lean_ctor_set(v___x_923_, 5, v___x_921_);
lean_ctor_set(v___x_923_, 6, v___x_921_);
lean_ctor_set(v___x_923_, 7, v___x_921_);
lean_ctor_set(v___x_923_, 8, v___x_921_);
lean_ctor_set(v___x_923_, 9, v___x_921_);
lean_ctor_set(v___x_923_, 10, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_925_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
lean_ctor_set(v___x_925_, 4, v___x_924_);
lean_ctor_set(v___x_925_, 5, v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
lean_ctor_set(v___x_927_, 4, v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v___f_963_, uint8_t v___x_964_, lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_a_967_, lean_object* v_declName_968_, lean_object* v_stx_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v_hint_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; 
v___x_979_ = l_Lean_Name_mkStr2(v___x_961_, v___x_962_);
lean_inc(v_stx_969_);
v___x_980_ = l_Lean_Syntax_isOfKind(v_stx_969_, v___x_979_);
lean_dec(v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v_stx_969_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1089_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1090_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1089_, v___y_970_, v___y_971_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v_val_1102_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; uint8_t v___y_1148_; uint8_t v_a_1149_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v_a_1299_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v_since_x3f_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v_typeChanged_x3f_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1355_; lean_object* v_text_x3f_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v_id_x3f_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1381_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_1092_);
v___x_1382_ = l_Lean_Syntax_isNone(v___x_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
lean_inc(v___x_1381_);
v___x_1383_ = l_Lean_Syntax_matchesNull(v___x_1381_, v___x_1092_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v___x_1381_);
lean_dec(v_stx_969_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1384_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1385_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1384_, v___y_970_, v___y_971_);
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = l_Lean_Syntax_getArg(v___x_1381_, v___x_1091_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
v_id_x3f_1369_ = v___x_1387_;
v___y_1370_ = v___y_970_;
v___y_1371_ = v___y_971_;
goto v___jp_1368_;
}
}
else
{
lean_object* v___x_1388_; 
lean_dec(v___x_1381_);
v___x_1388_ = lean_box(0);
v_id_x3f_1369_ = v___x_1388_;
v___y_1370_ = v___y_970_;
v___y_1371_ = v___y_971_;
goto v___jp_1368_;
}
v___jp_1093_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1103_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___f_963_);
v___x_1108_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1104_);
lean_ctor_set(v___x_1108_, 1, v___x_1105_);
lean_ctor_set(v___x_1108_, 2, v___x_1105_);
lean_ctor_set(v___x_1108_, 3, v___x_1105_);
lean_ctor_set(v___x_1108_, 4, v___x_1106_);
lean_ctor_set(v___x_1108_, 5, v___x_1107_);
lean_inc(v_val_1102_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_val_1102_);
lean_ctor_set(v___x_1109_, 1, v_val_1102_);
v___x_1110_ = l_Lean_Syntax_ofRange(v___x_1109_, v___x_980_);
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
v___x_1112_ = 4;
v___x_1113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1113_, 0, v___x_1108_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
lean_ctor_set(v___x_1113_, 2, v___x_1105_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3, v___x_1112_);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1092_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1113_);
v___x_1116_ = l_Lean_MessageData_hint(v___x_1103_, v___x_1115_, v___x_1105_, v___x_1105_, v___x_964_, v___y_1097_, v___y_1095_);
lean_dec_ref(v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___y_1049_ = v___y_1094_;
v___y_1050_ = v___y_1096_;
v___y_1051_ = v___y_1098_;
v___y_1052_ = v___y_1099_;
v___y_1053_ = v___y_1100_;
v___y_1054_ = v___y_1101_;
v_hint_1055_ = v_a_1117_;
v___y_1056_ = v___y_1097_;
v___y_1057_ = v___y_1095_;
goto v___jp_1048_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1094_);
v_a_1118_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1116_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
v___jp_1126_:
{
if (lean_obj_tag(v___y_1134_) == 0)
{
lean_dec_ref(v___f_963_);
v___y_1080_ = v___y_1127_;
v___y_1081_ = v___y_1128_;
v___y_1082_ = v___y_1130_;
v___y_1083_ = v___y_1129_;
v___y_1084_ = v___y_1131_;
v___y_1085_ = v___y_1132_;
v___y_1086_ = v___y_1133_;
v___y_1087_ = v___y_1134_;
goto v___jp_1079_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1136_; 
v_val_1135_ = lean_ctor_get(v___y_1134_, 0);
v___x_1136_ = l_Lean_Syntax_getTailPos_x3f(v_val_1135_, v___x_980_);
if (lean_obj_tag(v___x_1136_) == 1)
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___y_1094_ = v___y_1127_;
v___y_1095_ = v___y_1128_;
v___y_1096_ = v___y_1130_;
v___y_1097_ = v___y_1129_;
v___y_1098_ = v___y_1131_;
v___y_1099_ = v___y_1132_;
v___y_1100_ = v___y_1133_;
v___y_1101_ = v___y_1134_;
v_val_1102_ = v_val_1137_;
goto v___jp_1093_;
}
else
{
lean_dec(v___x_1136_);
lean_dec_ref(v___f_963_);
v___y_1080_ = v___y_1127_;
v___y_1081_ = v___y_1128_;
v___y_1082_ = v___y_1130_;
v___y_1083_ = v___y_1129_;
v___y_1084_ = v___y_1131_;
v___y_1085_ = v___y_1132_;
v___y_1086_ = v___y_1133_;
v___y_1087_ = v___y_1134_;
goto v___jp_1079_;
}
}
}
v___jp_1138_:
{
if (v_a_1149_ == 0)
{
if (lean_obj_tag(v___y_1145_) == 0)
{
if (v___y_1148_ == 0)
{
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1139_;
v___y_1033_ = v___y_1144_;
v___y_1034_ = v___y_1146_;
v___y_1035_ = v___y_1147_;
v___y_1036_ = v___y_1141_;
v___y_1037_ = v___y_1140_;
goto v___jp_1031_;
}
else
{
if (lean_obj_tag(v___y_1146_) == 0)
{
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
v___y_1130_ = v___y_1142_;
v___y_1131_ = v___y_1143_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1146_;
v___y_1134_ = v___y_1147_;
goto v___jp_1126_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1151_; 
v_val_1150_ = lean_ctor_get(v___y_1146_, 0);
v___x_1151_ = l_Lean_Syntax_getTailPos_x3f(v_val_1150_, v___x_980_);
if (lean_obj_tag(v___x_1151_) == 0)
{
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
v___y_1130_ = v___y_1142_;
v___y_1131_ = v___y_1143_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1146_;
v___y_1134_ = v___y_1147_;
goto v___jp_1126_;
}
else
{
lean_object* v_val_1152_; 
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___y_1094_ = v___y_1139_;
v___y_1095_ = v___y_1140_;
v___y_1096_ = v___y_1142_;
v___y_1097_ = v___y_1141_;
v___y_1098_ = v___y_1143_;
v___y_1099_ = v___y_1144_;
v___y_1100_ = v___y_1146_;
v___y_1101_ = v___y_1147_;
v_val_1102_ = v_val_1152_;
goto v___jp_1093_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_1145_, 1);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1139_;
v___y_1033_ = v___y_1144_;
v___y_1034_ = v___y_1146_;
v___y_1035_ = v___y_1147_;
v___y_1036_ = v___y_1141_;
v___y_1037_ = v___y_1140_;
goto v___jp_1031_;
}
}
else
{
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v___f_963_);
if (lean_obj_tag(v___y_1145_) == 0)
{
v___y_1032_ = v___y_1139_;
v___y_1033_ = v___y_1144_;
v___y_1034_ = v___y_1146_;
v___y_1035_ = v___y_1147_;
v___y_1036_ = v___y_1141_;
v___y_1037_ = v___y_1140_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref_known(v___y_1145_, 1);
v___x_1153_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1154_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_1153_, v___y_1141_, v___y_1140_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_dec_ref_known(v___x_1154_, 1);
v___y_1032_ = v___y_1139_;
v___y_1033_ = v___y_1144_;
v___y_1034_ = v___y_1146_;
v___y_1035_ = v___y_1147_;
v___y_1036_ = v___y_1141_;
v___y_1037_ = v___y_1140_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec(v___y_1144_);
lean_dec(v___y_1139_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
v___jp_1163_:
{
lean_object* v___x_1174_; 
lean_inc_ref(v___y_1170_);
v___x_1174_ = l_Lean_Environment_find_x3f(v___y_1170_, v_declName_968_, v___x_964_);
if (lean_obj_tag(v___x_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v___x_1176_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Lean_Environment_find_x3f(v___y_1170_, v___y_1167_, v___x_964_);
if (lean_obj_tag(v___x_1176_) == 1)
{
lean_object* v_val_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; uint64_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_val_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = 1;
v___x_1179_ = 0;
v___x_1180_ = 2;
v___x_1181_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1181_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 1, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 2, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 3, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 4, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 5, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 6, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 7, v___x_964_);
lean_ctor_set_uint8(v___x_1181_, 8, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 9, v___x_1178_);
lean_ctor_set_uint8(v___x_1181_, 10, v___x_1179_);
lean_ctor_set_uint8(v___x_1181_, 11, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 12, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 13, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 14, v___x_1180_);
lean_ctor_set_uint8(v___x_1181_, 15, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 16, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 17, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 18, v___y_1171_);
lean_ctor_set_uint8(v___x_1181_, 19, v___x_964_);
v___x_1182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set_uint64(v___x_1183_, sizeof(void*)*1, v___x_1182_);
v___x_1184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1185_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1187_ = lean_box(0);
lean_inc(v___x_965_);
v___x_1188_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1188_, 0, v___x_1183_);
lean_ctor_set(v___x_1188_, 1, v___x_965_);
lean_ctor_set(v___x_1188_, 2, v___x_1185_);
lean_ctor_set(v___x_1188_, 3, v___x_1186_);
lean_ctor_set(v___x_1188_, 4, v___x_1187_);
lean_ctor_set(v___x_1188_, 5, v___x_1091_);
lean_ctor_set(v___x_1188_, 6, v___x_1187_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*7, v___x_964_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*7 + 1, v___x_964_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*7 + 2, v___x_964_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*7 + 3, v___x_980_);
v___x_1189_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1190_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1191_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1189_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v___x_965_);
lean_ctor_set(v___x_1192_, 3, v___x_1184_);
lean_ctor_set(v___x_1192_, 4, v___x_1191_);
v___x_1193_ = lean_st_mk_ref(v___x_1192_);
v___x_1194_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_1175_, v_val_1177_, v___x_1188_, v___x_1193_, v___y_1172_, v___y_1173_);
lean_dec_ref_known(v___x_1188_, 7);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = lean_st_ref_get(v___x_1193_);
lean_dec(v___x_1193_);
lean_dec(v___x_1196_);
v___x_1197_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___y_1173_;
v___y_1141_ = v___y_1172_;
v___y_1142_ = v_val_1175_;
v___y_1143_ = v_val_1177_;
v___y_1144_ = v___y_1165_;
v___y_1145_ = v___y_1166_;
v___y_1146_ = v___y_1168_;
v___y_1147_ = v___y_1169_;
v___y_1148_ = v___y_1171_;
v_a_1149_ = v___x_1197_;
goto v___jp_1138_;
}
else
{
lean_dec(v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1198_; uint8_t v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1199_ = lean_unbox(v_a_1198_);
lean_dec(v_a_1198_);
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___y_1173_;
v___y_1141_ = v___y_1172_;
v___y_1142_ = v_val_1175_;
v___y_1143_ = v_val_1177_;
v___y_1144_ = v___y_1165_;
v___y_1145_ = v___y_1166_;
v___y_1146_ = v___y_1168_;
v___y_1147_ = v___y_1169_;
v___y_1148_ = v___y_1171_;
v_a_1149_ = v___x_1199_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_val_1177_);
lean_dec(v_val_1175_);
lean_dec(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___f_963_);
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_dec(v___x_1176_);
lean_dec(v_val_1175_);
lean_dec(v___y_1166_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1164_;
v___y_1033_ = v___y_1165_;
v___y_1034_ = v___y_1168_;
v___y_1035_ = v___y_1169_;
v___y_1036_ = v___y_1172_;
v___y_1037_ = v___y_1173_;
goto v___jp_1031_;
}
}
else
{
lean_dec(v___x_1174_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1164_;
v___y_1033_ = v___y_1165_;
v___y_1034_ = v___y_1168_;
v___y_1035_ = v___y_1169_;
v___y_1036_ = v___y_1172_;
v___y_1037_ = v___y_1173_;
goto v___jp_1031_;
}
}
v___jp_1208_:
{
if (lean_obj_tag(v___y_1209_) == 1)
{
lean_object* v_val_1216_; lean_object* v___x_1217_; 
v_val_1216_ = lean_ctor_get(v___y_1209_, 0);
lean_inc(v_val_1216_);
v___x_1217_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2(v_val_1216_, v___x_964_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
lean_dec_ref_known(v___x_1217_, 1);
v___x_1218_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3(v___y_1214_, v___y_1215_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l_Lean_Linter_linter_deprecated;
v___x_1221_ = l_Lean_Linter_getLinterValue(v___x_1220_, v_a_1219_);
lean_dec(v_a_1219_);
if (v___x_1221_ == 0)
{
lean_dec(v___y_1211_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1209_;
v___y_1033_ = v___y_1210_;
v___y_1034_ = v___y_1212_;
v___y_1035_ = v___y_1213_;
v___y_1036_ = v___y_1214_;
v___y_1037_ = v___y_1215_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v_options_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
lean_inc(v_val_1216_);
v___x_1222_ = lean_st_ref_get(v___y_1215_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v_options_1224_ = lean_ctor_get(v___y_1214_, 2);
v___x_1225_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_1226_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_dec_ref(v___x_966_);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1227_; 
lean_inc(v_val_1216_);
lean_inc_ref(v_env_1223_);
v___x_1227_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_966_, v_a_967_, v___x_964_, v_env_1223_, v_val_1216_);
if (lean_obj_tag(v___x_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v_name_1229_; lean_object* v_newName_x3f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v_name_1229_ = lean_ctor_get(v___x_1225_, 0);
v_newName_x3f_1230_ = lean_ctor_get(v_val_1228_, 0);
lean_inc(v_newName_x3f_1230_);
lean_dec(v_val_1228_);
v___x_1231_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
lean_inc(v_name_1229_);
v___x_1232_ = l_Lean_MessageData_ofName(v_name_1229_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_MessageData_note(v___x_1235_);
if (lean_obj_tag(v_newName_x3f_1230_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1237_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
lean_inc(v_val_1216_);
v___x_1238_ = l_Lean_MessageData_ofConstName(v_val_1216_, v___x_980_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc(v_declName_968_);
v___x_1242_ = l_Lean_MessageData_ofConstName(v_declName_968_, v___x_980_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1236_);
v___x_1247_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_1246_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_dec_ref_known(v___x_1247_, 1);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_env_1223_);
lean_dec(v_val_1216_);
lean_dec_ref_known(v___y_1209_, 1);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_declName_968_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_val_1256_; uint8_t v___x_1257_; 
v_val_1256_ = lean_ctor_get(v_newName_x3f_1230_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v_newName_x3f_1230_, 1);
v___x_1257_ = lean_name_eq(v_val_1256_, v_val_1216_);
if (v___x_1257_ == 0)
{
if (v___x_1226_ == 0)
{
lean_dec(v_val_1256_);
lean_dec_ref(v___x_1236_);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1258_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
lean_inc(v_val_1216_);
v___x_1259_ = l_Lean_MessageData_ofConstName(v_val_1216_, v___x_980_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Lean_MessageData_ofConstName(v_val_1256_, v___x_980_);
lean_inc_ref(v___x_1263_);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_inc(v_declName_968_);
v___x_1267_ = l_Lean_MessageData_ofConstName(v_declName_968_, v___x_980_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1263_);
v___x_1272_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1236_);
v___x_1275_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_1274_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref_known(v___x_1275_, 1);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_env_1223_);
lean_dec(v_val_1216_);
lean_dec_ref_known(v___y_1209_, 1);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_declName_968_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_dec(v_val_1256_);
lean_dec_ref(v___x_1236_);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
}
}
else
{
lean_dec(v___x_1227_);
v___y_1164_ = v___y_1209_;
v___y_1165_ = v___y_1210_;
v___y_1166_ = v___y_1211_;
v___y_1167_ = v_val_1216_;
v___y_1168_ = v___y_1212_;
v___y_1169_ = v___y_1213_;
v___y_1170_ = v_env_1223_;
v___y_1171_ = v___x_1221_;
v___y_1172_ = v___y_1214_;
v___y_1173_ = v___y_1215_;
goto v___jp_1163_;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref_known(v___y_1209_, 1);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v_a_1284_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1217_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1217_);
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
else
{
lean_dec(v___y_1211_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___y_1032_ = v___y_1209_;
v___y_1033_ = v___y_1210_;
v___y_1034_ = v___y_1212_;
v___y_1035_ = v___y_1213_;
v___y_1036_ = v___y_1214_;
v___y_1037_ = v___y_1215_;
goto v___jp_1031_;
}
}
v___jp_1292_:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
lean_inc(v_declName_968_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_declName_968_);
v___x_1301_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__5(v_a_1299_, v___x_1300_);
lean_dec_ref_known(v___x_1300_, 1);
if (v___x_1301_ == 0)
{
v___y_1209_ = v_a_1299_;
v___y_1210_ = v___y_1295_;
v___y_1211_ = v___y_1296_;
v___y_1212_ = v___y_1297_;
v___y_1213_ = v___y_1298_;
v___y_1214_ = v___y_1293_;
v___y_1215_ = v___y_1294_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1299_);
lean_dec(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1302_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1303_ = l_Lean_MessageData_ofConstName(v_declName_968_, v___x_980_);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1306_, v___y_1293_, v___y_1294_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
v___jp_1316_:
{
if (lean_obj_tag(v___y_1319_) == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_box(0);
v___y_1293_ = v___y_1321_;
v___y_1294_ = v___y_1322_;
v___y_1295_ = v_since_x3f_1320_;
v___y_1296_ = v___y_1317_;
v___y_1297_ = v___y_1318_;
v___y_1298_ = v___y_1319_;
v_a_1299_ = v___x_1323_;
goto v___jp_1292_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_val_1324_ = lean_ctor_get(v___y_1319_, 0);
v___x_1325_ = lean_box(0);
lean_inc(v_val_1324_);
v___x_1326_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_1324_, v___x_1325_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_a_1327_);
v___y_1293_ = v___y_1321_;
v___y_1294_ = v___y_1322_;
v___y_1295_ = v_since_x3f_1320_;
v___y_1296_ = v___y_1317_;
v___y_1297_ = v___y_1318_;
v___y_1298_ = v___y_1319_;
v_a_1299_ = v___x_1328_;
goto v___jp_1292_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref_known(v___y_1319_, 1);
lean_dec(v_since_x3f_1320_);
lean_dec(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v_a_1329_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1326_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1326_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
v___jp_1337_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_unsigned_to_nat(4u);
v___x_1345_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_1344_);
lean_dec(v_stx_969_);
v___x_1346_ = l_Lean_Syntax_isNone(v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1345_);
v___x_1348_ = l_Lean_Syntax_matchesNull(v___x_1345_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v___x_1345_);
lean_dec(v_typeChanged_x3f_1341_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1349_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1350_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1349_, v___y_1342_, v___y_1343_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = l_Lean_Syntax_getArg(v___x_1345_, v___y_1340_);
lean_dec(v___x_1345_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
v___y_1317_ = v_typeChanged_x3f_1341_;
v___y_1318_ = v___y_1338_;
v___y_1319_ = v___y_1339_;
v_since_x3f_1320_ = v___x_1352_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1343_;
goto v___jp_1316_;
}
}
else
{
lean_object* v___x_1353_; 
lean_dec(v___x_1345_);
v___x_1353_ = lean_box(0);
v___y_1317_ = v_typeChanged_x3f_1341_;
v___y_1318_ = v___y_1338_;
v___y_1319_ = v___y_1339_;
v_since_x3f_1320_ = v___x_1353_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1343_;
goto v___jp_1316_;
}
}
v___jp_1354_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(3u);
v___x_1360_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_1359_);
v___x_1361_ = l_Lean_Syntax_isNone(v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; 
lean_inc(v___x_1360_);
v___x_1362_ = l_Lean_Syntax_matchesNull(v___x_1360_, v___x_1092_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v___x_1360_);
lean_dec(v_text_x3f_1356_);
lean_dec(v___y_1355_);
lean_dec(v_stx_969_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1363_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1364_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1363_, v___y_1357_, v___y_1358_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = l_Lean_Syntax_getArg(v___x_1360_, v___x_1091_);
lean_dec(v___x_1360_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
v___y_1338_ = v_text_x3f_1356_;
v___y_1339_ = v___y_1355_;
v___y_1340_ = v___x_1359_;
v_typeChanged_x3f_1341_ = v___x_1366_;
v___y_1342_ = v___y_1357_;
v___y_1343_ = v___y_1358_;
goto v___jp_1337_;
}
}
else
{
lean_object* v___x_1367_; 
lean_dec(v___x_1360_);
v___x_1367_ = lean_box(0);
v___y_1338_ = v_text_x3f_1356_;
v___y_1339_ = v___y_1355_;
v___y_1340_ = v___x_1359_;
v_typeChanged_x3f_1341_ = v___x_1367_;
v___y_1342_ = v___y_1357_;
v___y_1343_ = v___y_1358_;
goto v___jp_1337_;
}
}
v___jp_1368_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(2u);
v___x_1373_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_isNone(v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
lean_inc(v___x_1373_);
v___x_1375_ = l_Lean_Syntax_matchesNull(v___x_1373_, v___x_1092_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v___x_1373_);
lean_dec(v_id_x3f_1369_);
lean_dec(v_stx_969_);
lean_dec(v_declName_968_);
lean_dec_ref(v___x_966_);
lean_dec(v___x_965_);
lean_dec_ref(v___f_963_);
v___x_1376_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1377_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v___x_1376_, v___y_1370_, v___y_1371_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = l_Lean_Syntax_getArg(v___x_1373_, v___x_1091_);
lean_dec(v___x_1373_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
v___y_1355_ = v_id_x3f_1369_;
v_text_x3f_1356_ = v___x_1379_;
v___y_1357_ = v___y_1370_;
v___y_1358_ = v___y_1371_;
goto v___jp_1354_;
}
}
else
{
lean_object* v___x_1380_; 
lean_dec(v___x_1373_);
v___x_1380_ = lean_box(0);
v___y_1355_ = v_id_x3f_1369_;
v_text_x3f_1356_ = v___x_1380_;
v___y_1357_ = v___y_1370_;
v___y_1358_ = v___y_1371_;
goto v___jp_1354_;
}
}
}
v___jp_973_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_977_, 0, v___y_974_);
lean_ctor_set(v___x_977_, 1, v___y_976_);
lean_ctor_set(v___x_977_, 2, v___y_975_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
v___jp_981_:
{
if (lean_obj_tag(v___y_983_) == 0)
{
if (v___x_980_ == 0)
{
v___y_974_ = v___y_982_;
v___y_975_ = v___y_983_;
v___y_976_ = v___y_984_;
goto v___jp_973_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_988_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_987_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_dec_ref_known(v___x_988_, 1);
v___y_974_ = v___y_982_;
v___y_975_ = v___y_983_;
v___y_976_ = v___y_984_;
goto v___jp_973_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v___y_984_);
lean_dec(v___y_982_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
else
{
v___y_974_ = v___y_982_;
v___y_975_ = v___y_983_;
v___y_976_ = v___y_984_;
goto v___jp_973_;
}
}
v___jp_997_:
{
if (lean_obj_tag(v___y_1002_) == 0)
{
if (v___x_980_ == 0)
{
v___y_982_ = v___y_999_;
v___y_983_ = v___y_1003_;
v___y_984_ = v___y_1001_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_1000_;
goto v___jp_981_;
}
else
{
if (lean_obj_tag(v___y_1001_) == 0)
{
if (v___x_980_ == 0)
{
v___y_982_ = v___y_999_;
v___y_983_ = v___y_1003_;
v___y_984_ = v___y_1001_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_1000_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1005_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_1004_, v___y_998_, v___y_1000_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
v___y_982_ = v___y_999_;
v___y_983_ = v___y_1003_;
v___y_984_ = v___y_1001_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_1000_;
goto v___jp_981_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v___y_1003_);
lean_dec(v___y_999_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
v___y_982_ = v___y_999_;
v___y_983_ = v___y_1003_;
v___y_984_ = v___y_1001_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_1000_;
goto v___jp_981_;
}
}
}
else
{
lean_dec_ref_known(v___y_1002_, 1);
v___y_982_ = v___y_999_;
v___y_983_ = v___y_1003_;
v___y_984_ = v___y_1001_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_1000_;
goto v___jp_981_;
}
}
v___jp_1014_:
{
if (lean_obj_tag(v___y_1018_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
v___y_998_ = v___y_1016_;
v___y_999_ = v___y_1015_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1020_;
v___y_1002_ = v___y_1019_;
v___y_1003_ = v___x_1021_;
goto v___jp_997_;
}
else
{
lean_object* v_val_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_val_1022_ = lean_ctor_get(v___y_1018_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___y_1018_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___y_1018_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_val_1022_);
lean_dec(v___y_1018_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_TSyntax_getString(v_val_1022_);
lean_dec(v_val_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
v___y_998_ = v___y_1016_;
v___y_999_ = v___y_1015_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1020_;
v___y_1002_ = v___y_1019_;
v___y_1003_ = v___x_1028_;
goto v___jp_997_;
}
}
}
}
v___jp_1031_:
{
if (lean_obj_tag(v___y_1034_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
v___y_1015_ = v___y_1032_;
v___y_1016_ = v___y_1036_;
v___y_1017_ = v___y_1037_;
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1035_;
v___y_1020_ = v___x_1038_;
goto v___jp_1014_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1047_; 
v_val_1039_ = lean_ctor_get(v___y_1034_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___y_1034_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1041_ = v___y_1034_;
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v___y_1034_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_TSyntax_getString(v_val_1039_);
lean_dec(v_val_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
v___y_1015_ = v___y_1032_;
v___y_1016_ = v___y_1036_;
v___y_1017_ = v___y_1037_;
v___y_1018_ = v___y_1033_;
v___y_1019_ = v___y_1035_;
v___y_1020_ = v___x_1045_;
goto v___jp_1014_;
}
}
}
}
v___jp_1048_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1058_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1059_ = l_Lean_ConstantInfo_type(v___y_1051_);
lean_dec_ref(v___y_1051_);
v___x_1060_ = l_Lean_indentExpr(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1058_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_ConstantInfo_type(v___y_1050_);
lean_dec_ref(v___y_1050_);
v___x_1065_ = l_Lean_indentExpr(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_hint_1055_);
v___x_1070_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1(v___x_1069_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_dec_ref_known(v___x_1070_, 1);
v___y_1032_ = v___y_1049_;
v___y_1033_ = v___y_1052_;
v___y_1034_ = v___y_1053_;
v___y_1035_ = v___y_1054_;
v___y_1036_ = v___y_1056_;
v___y_1037_ = v___y_1057_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1049_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
v___jp_1079_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___y_1049_ = v___y_1080_;
v___y_1050_ = v___y_1082_;
v___y_1051_ = v___y_1084_;
v___y_1052_ = v___y_1085_;
v___y_1053_ = v___y_1086_;
v___y_1054_ = v___y_1087_;
v_hint_1055_ = v___x_1088_;
v___y_1056_ = v___y_1083_;
v___y_1057_ = v___y_1081_;
goto v___jp_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___f_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v_a_1395_, lean_object* v_declName_1396_, lean_object* v_stx_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v___x_16437__boxed_1401_; lean_object* v_res_1402_; 
v___x_16437__boxed_1401_ = lean_unbox(v___x_1392_);
v_res_1402_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(v___x_1389_, v___x_1390_, v___f_1391_, v___x_16437__boxed_1401_, v___x_1393_, v___x_1394_, v_a_1395_, v_declName_1396_, v_stx_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v_a_1395_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_1423_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1424_ = 0;
v___f_1425_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1426_ = l_Lean_registerParametricAttributeExt___redArg(v___x_1423_, v___x_1424_, v___f_1425_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_n(v_a_1427_, 2);
lean_dec_ref_known(v___x_1426_, 1);
v___f_1428_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___f_1429_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1430_ = lean_box(1);
v___x_1431_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1432_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_1433_ = lean_box(v___x_1424_);
v___f_1434_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_1434_, 0, v___x_1422_);
lean_closure_set(v___f_1434_, 1, v___x_1432_);
lean_closure_set(v___f_1434_, 2, v___f_1428_);
lean_closure_set(v___f_1434_, 3, v___x_1433_);
lean_closure_set(v___f_1434_, 4, v___x_1430_);
lean_closure_set(v___f_1434_, 5, v___x_1431_);
lean_closure_set(v___f_1434_, 6, v_a_1427_);
v___x_1435_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1436_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___f_1434_);
lean_ctor_set(v___x_1436_, 2, v___f_1429_);
lean_ctor_set(v___x_1436_, 3, v___f_1425_);
lean_ctor_set_uint8(v___x_1436_, sizeof(void*)*4, v___x_1424_);
v___x_1437_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_1436_, v_a_1427_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1426_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1426_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2____boxed(lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_();
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___redArg(v_msg_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__0(v_00_u03b1_1454_, v_msg_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1460_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__3_spec__8(v_o_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_1470_, lean_object* v_m_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_1471_, v_a_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_1474_, lean_object* v_m_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_1474_, v_m_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_m_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_1482_, v_x_1483_, v_x_1484_);
lean_dec_ref(v_x_1484_);
lean_dec_ref(v_x_1483_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_1488_, v_x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_1491_, v_a_1492_, v_x_1493_);
lean_dec(v_x_1493_);
lean_dec(v_a_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1495_, lean_object* v_x_1496_, size_t v_x_1497_, lean_object* v_x_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___redArg(v_x_1496_, v_x_1497_, v_x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
size_t v_x_17535__boxed_1504_; uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_x_17535__boxed_1504_ = lean_unbox_usize(v_x_1502_);
lean_dec(v_x_1502_);
v_res_1505_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11(v_00_u03b2_1500_, v_x_1501_, v_x_17535__boxed_1504_, v_x_1503_);
lean_dec_ref(v_x_1503_);
lean_dec_ref(v_x_1501_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14(lean_object* v_00_u03b2_1507_, lean_object* v_keys_1508_, lean_object* v_vals_1509_, lean_object* v_heq_1510_, lean_object* v_i_1511_, lean_object* v_k_1512_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___redArg(v_keys_1508_, v_i_1511_, v_k_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14___boxed(lean_object* v_00_u03b2_1514_, lean_object* v_keys_1515_, lean_object* v_vals_1516_, lean_object* v_heq_1517_, lean_object* v_i_1518_, lean_object* v_k_1519_){
_start:
{
uint8_t v_res_1520_; lean_object* v_r_1521_; 
v_res_1520_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__11_spec__14(v_00_u03b2_1514_, v_keys_1515_, v_vals_1516_, v_heq_1517_, v_i_1518_, v_k_1519_);
lean_dec_ref(v_k_1519_);
lean_dec_ref(v_vals_1516_);
lean_dec_ref(v_keys_1515_);
v_r_1521_ = lean_box(v_res_1520_);
return v_r_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_1522_, lean_object* v_entry_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_env_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l_Lean_Linter_deprecatedAttr;
v___x_1529_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1528_, v_env_1527_, v_declName_1522_, v_entry_1523_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_inst_1526_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = l_Lean_MessageData_ofFormat(v___x_1535_);
v___x_1537_ = l_Lean_throwError___redArg(v_inst_1524_, v_inst_1525_, v___x_1536_);
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_inst_1524_);
v_a_1540_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1541_ = l_Lean_setEnv___redArg(v_inst_1526_, v_a_1540_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_declName_1545_, lean_object* v_entry_1546_){
_start:
{
lean_object* v_toBind_1547_; lean_object* v_getEnv_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; 
v_toBind_1547_ = lean_ctor_get(v_inst_1542_, 1);
lean_inc(v_toBind_1547_);
v_getEnv_1548_ = lean_ctor_get(v_inst_1543_, 0);
lean_inc(v_getEnv_1548_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1549_, 0, v_declName_1545_);
lean_closure_set(v___f_1549_, 1, v_entry_1546_);
lean_closure_set(v___f_1549_, 2, v_inst_1542_);
lean_closure_set(v___f_1549_, 3, v_inst_1544_);
lean_closure_set(v___f_1549_, 4, v_inst_1543_);
v___x_1550_ = lean_apply_4(v_toBind_1547_, lean_box(0), lean_box(0), v_getEnv_1548_, v___f_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_declName_1555_, lean_object* v_entry_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Linter_setDeprecated___redArg(v_inst_1552_, v_inst_1553_, v_inst_1554_, v_declName_1555_, v_entry_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_1558_, lean_object* v_declName_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1561_ = l_Lean_Linter_deprecatedAttr;
v___x_1562_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1560_, v___x_1561_, v_env_1558_, v_declName_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = 0;
return v___x_1563_;
}
else
{
uint8_t v___x_1564_; 
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = 1;
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_1565_, lean_object* v_declName_1566_){
_start:
{
uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_res_1567_ = l_Lean_Linter_isDeprecated(v_env_1565_, v_declName_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_1569_){
_start:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_1571_ = lean_name_eq(v_x_1569_, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_1572_);
lean_dec(v_x_1572_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_1576_){
_start:
{
lean_object* v___f_1577_; uint8_t v___x_1578_; 
v___f_1577_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_1578_ = l_Lean_MessageData_hasTag(v___f_1577_, v_msg_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_Lean_MessageData_isDeprecationWarning(v_msg_1579_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_1582_, lean_object* v_declName_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1585_ = l_Lean_Linter_deprecatedAttr;
v___x_1586_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1584_, v___x_1585_, v_env_1582_, v_declName_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_box(0);
return v___x_1587_;
}
else
{
lean_object* v_val_1588_; lean_object* v_newName_x3f_1589_; 
v_val_1588_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1586_, 1);
v_newName_x3f_1589_ = lean_ctor_get(v_val_1588_, 0);
lean_inc(v_newName_x3f_1589_);
lean_dec(v_val_1588_);
return v_newName_x3f_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(lean_object* v___x_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1590_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed(lean_object* v___x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(v___x_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_1604_){
_start:
{
if (lean_obj_tag(v_x_1604_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_box(0);
return v___x_1605_;
}
else
{
lean_object* v_head_1606_; lean_object* v_tail_1607_; lean_object* v_fst_1608_; uint8_t v___x_1609_; 
v_head_1606_ = lean_ctor_get(v_x_1604_, 0);
v_tail_1607_ = lean_ctor_get(v_x_1604_, 1);
v_fst_1608_ = lean_ctor_get(v_head_1606_, 0);
v___x_1609_ = l_Lean_isPrivateName(v_fst_1608_);
if (v___x_1609_ == 0)
{
v_x_1604_ = v_tail_1607_;
goto _start;
}
else
{
lean_object* v___x_1611_; 
lean_inc(v_head_1606_);
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_head_1606_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_1612_);
lean_dec(v_x_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(lean_object* v_msgData_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v_env_1621_; lean_object* v___x_1622_; lean_object* v_mctx_1623_; lean_object* v_lctx_1624_; lean_object* v_options_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1620_ = lean_st_ref_get(v___y_1618_);
v_env_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc_ref(v_env_1621_);
lean_dec(v___x_1620_);
v___x_1622_ = lean_st_ref_get(v___y_1616_);
v_mctx_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_mctx_1623_);
lean_dec(v___x_1622_);
v_lctx_1624_ = lean_ctor_get(v___y_1615_, 2);
v_options_1625_ = lean_ctor_get(v___y_1617_, 2);
lean_inc_ref(v_options_1625_);
lean_inc_ref(v_lctx_1624_);
v___x_1626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1626_, 0, v_env_1621_);
lean_ctor_set(v___x_1626_, 1, v_mctx_1623_);
lean_ctor_set(v___x_1626_, 2, v_lctx_1624_);
lean_ctor_set(v___x_1626_, 3, v_options_1625_);
v___x_1627_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_msgData_1614_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19___boxed(lean_object* v_msgData_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v_msgData_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(lean_object* v_ref_1638_, lean_object* v_msgData_1639_, uint8_t v_severity_1640_, uint8_t v_isSilent_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_a_1648_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; uint8_t v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1722_; lean_object* v___y_1723_; uint8_t v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; uint8_t v___x_1733_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; uint8_t v___y_1741_; uint8_t v___y_1743_; uint8_t v___x_1758_; 
v___x_1733_ = 2;
v___x_1758_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1640_, v___x_1733_);
if (v___x_1758_ == 0)
{
v___y_1743_ = v___x_1758_;
goto v___jp_1742_;
}
else
{
uint8_t v___x_1759_; 
lean_inc_ref(v_msgData_1639_);
v___x_1759_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1639_);
v___y_1743_ = v___x_1759_;
goto v___jp_1742_;
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_a_1648_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
v___jp_1651_:
{
lean_object* v___x_1661_; lean_object* v_currNamespace_1662_; lean_object* v_openDecls_1663_; lean_object* v_env_1664_; lean_object* v_nextMacroScope_1665_; lean_object* v_ngen_1666_; lean_object* v_auxDeclNGen_1667_; lean_object* v_traceState_1668_; lean_object* v_cache_1669_; lean_object* v_messages_1670_; lean_object* v_infoState_1671_; lean_object* v_snapshotTasks_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1685_; 
v___x_1661_ = lean_st_ref_take(v___y_1660_);
v_currNamespace_1662_ = lean_ctor_get(v___y_1659_, 6);
v_openDecls_1663_ = lean_ctor_get(v___y_1659_, 7);
v_env_1664_ = lean_ctor_get(v___x_1661_, 0);
v_nextMacroScope_1665_ = lean_ctor_get(v___x_1661_, 1);
v_ngen_1666_ = lean_ctor_get(v___x_1661_, 2);
v_auxDeclNGen_1667_ = lean_ctor_get(v___x_1661_, 3);
v_traceState_1668_ = lean_ctor_get(v___x_1661_, 4);
v_cache_1669_ = lean_ctor_get(v___x_1661_, 5);
v_messages_1670_ = lean_ctor_get(v___x_1661_, 6);
v_infoState_1671_ = lean_ctor_get(v___x_1661_, 7);
v_snapshotTasks_1672_ = lean_ctor_get(v___x_1661_, 8);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_snapshotTasks_1672_);
lean_inc(v_infoState_1671_);
lean_inc(v_messages_1670_);
lean_inc(v_cache_1669_);
lean_inc(v_traceState_1668_);
lean_inc(v_auxDeclNGen_1667_);
lean_inc(v_ngen_1666_);
lean_inc(v_nextMacroScope_1665_);
lean_inc(v_env_1664_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_inc(v_openDecls_1663_);
lean_inc(v_currNamespace_1662_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_currNamespace_1662_);
lean_ctor_set(v___x_1676_, 1, v_openDecls_1663_);
v___x_1677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc_ref(v___y_1653_);
v___x_1678_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1678_, 0, v___y_1653_);
lean_ctor_set(v___x_1678_, 1, v___y_1657_);
lean_ctor_set(v___x_1678_, 2, v___y_1658_);
lean_ctor_set(v___x_1678_, 3, v___y_1654_);
lean_ctor_set(v___x_1678_, 4, v___x_1677_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*5, v___y_1656_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*5 + 1, v___y_1652_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*5 + 2, v_isSilent_1641_);
v___x_1679_ = l_Lean_MessageLog_add(v___x_1678_, v_messages_1670_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 6, v___x_1679_);
v___x_1681_ = v___x_1674_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_env_1664_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_nextMacroScope_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_ngen_1666_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_auxDeclNGen_1667_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_traceState_1668_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v_cache_1669_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v_infoState_1671_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_snapshotTasks_1672_);
v___x_1681_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_st_ref_put(v___y_1660_, v___x_1681_);
v___x_1683_ = lean_box(0);
v_a_1648_ = v___x_1683_;
goto v___jp_1647_;
}
}
}
v___jp_1686_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1709_; 
v___x_1695_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1639_);
v___x_1696_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_1695_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1709_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1709_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_inc_ref_n(v___y_1691_, 2);
v___x_1701_ = l_Lean_FileMap_toPosition(v___y_1691_, v___y_1693_);
lean_dec(v___y_1693_);
v___x_1702_ = l_Lean_FileMap_toPosition(v___y_1691_, v___y_1694_);
lean_dec(v___y_1694_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 1);
lean_ctor_set(v___x_1699_, 0, v___x_1702_);
v___x_1704_ = v___x_1699_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_1690_ == 0)
{
lean_dec_ref(v___y_1687_);
v___y_1652_ = v___y_1688_;
v___y_1653_ = v___y_1689_;
v___y_1654_ = v___x_1705_;
v___y_1655_ = v_a_1697_;
v___y_1656_ = v___y_1692_;
v___y_1657_ = v___x_1701_;
v___y_1658_ = v___x_1704_;
v___y_1659_ = v___y_1644_;
v___y_1660_ = v___y_1645_;
goto v___jp_1651_;
}
else
{
uint8_t v___x_1706_; 
lean_inc(v_a_1697_);
v___x_1706_ = l_Lean_MessageData_hasTag(v___y_1687_, v_a_1697_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_dec_ref(v___x_1704_);
lean_dec_ref(v___x_1701_);
lean_dec(v_a_1697_);
v___x_1707_ = lean_box(0);
v_a_1648_ = v___x_1707_;
goto v___jp_1647_;
}
else
{
v___y_1652_ = v___y_1688_;
v___y_1653_ = v___y_1689_;
v___y_1654_ = v___x_1705_;
v___y_1655_ = v_a_1697_;
v___y_1656_ = v___y_1692_;
v___y_1657_ = v___x_1701_;
v___y_1658_ = v___x_1704_;
v___y_1659_ = v___y_1644_;
v___y_1660_ = v___y_1645_;
goto v___jp_1651_;
}
}
}
}
}
v___jp_1710_:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Syntax_getTailPos_x3f(v___y_1717_, v___y_1716_);
lean_dec(v___y_1717_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_inc(v___y_1718_);
v___y_1687_ = v___y_1711_;
v___y_1688_ = v___y_1712_;
v___y_1689_ = v___y_1713_;
v___y_1690_ = v___y_1715_;
v___y_1691_ = v___y_1714_;
v___y_1692_ = v___y_1716_;
v___y_1693_ = v___y_1718_;
v___y_1694_ = v___y_1718_;
goto v___jp_1686_;
}
else
{
lean_object* v_val_1720_; 
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___y_1687_ = v___y_1711_;
v___y_1688_ = v___y_1712_;
v___y_1689_ = v___y_1713_;
v___y_1690_ = v___y_1715_;
v___y_1691_ = v___y_1714_;
v___y_1692_ = v___y_1716_;
v___y_1693_ = v___y_1718_;
v___y_1694_ = v_val_1720_;
goto v___jp_1686_;
}
}
v___jp_1721_:
{
lean_object* v_ref_1729_; lean_object* v___x_1730_; 
v_ref_1729_ = l_Lean_replaceRef(v_ref_1638_, v___y_1727_);
v___x_1730_ = l_Lean_Syntax_getPos_x3f(v_ref_1729_, v___y_1726_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___y_1711_ = v___y_1722_;
v___y_1712_ = v___y_1728_;
v___y_1713_ = v___y_1723_;
v___y_1714_ = v___y_1725_;
v___y_1715_ = v___y_1724_;
v___y_1716_ = v___y_1726_;
v___y_1717_ = v_ref_1729_;
v___y_1718_ = v___x_1731_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1732_; 
v_val_1732_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v___x_1730_, 1);
v___y_1711_ = v___y_1722_;
v___y_1712_ = v___y_1728_;
v___y_1713_ = v___y_1723_;
v___y_1714_ = v___y_1725_;
v___y_1715_ = v___y_1724_;
v___y_1716_ = v___y_1726_;
v___y_1717_ = v_ref_1729_;
v___y_1718_ = v_val_1732_;
goto v___jp_1710_;
}
}
v___jp_1734_:
{
if (v___y_1741_ == 0)
{
v___y_1722_ = v___y_1738_;
v___y_1723_ = v___y_1735_;
v___y_1724_ = v___y_1737_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1740_;
v___y_1727_ = v___y_1739_;
v___y_1728_ = v_severity_1640_;
goto v___jp_1721_;
}
else
{
v___y_1722_ = v___y_1738_;
v___y_1723_ = v___y_1735_;
v___y_1724_ = v___y_1737_;
v___y_1725_ = v___y_1736_;
v___y_1726_ = v___y_1740_;
v___y_1727_ = v___y_1739_;
v___y_1728_ = v___x_1733_;
goto v___jp_1721_;
}
}
v___jp_1742_:
{
if (v___y_1743_ == 0)
{
lean_object* v_fileName_1744_; lean_object* v_fileMap_1745_; lean_object* v_options_1746_; lean_object* v_ref_1747_; uint8_t v_suppressElabErrors_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; 
v_fileName_1744_ = lean_ctor_get(v___y_1644_, 0);
v_fileMap_1745_ = lean_ctor_get(v___y_1644_, 1);
v_options_1746_ = lean_ctor_get(v___y_1644_, 2);
v_ref_1747_ = lean_ctor_get(v___y_1644_, 5);
v_suppressElabErrors_1748_ = lean_ctor_get_uint8(v___y_1644_, sizeof(void*)*14 + 1);
v___x_1749_ = lean_box(v_suppressElabErrors_1748_);
v___x_1750_ = lean_box(v___y_1743_);
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1751_, 0, v___x_1749_);
lean_closure_set(v___f_1751_, 1, v___x_1750_);
v___x_1752_ = 1;
v___x_1753_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1640_, v___x_1752_);
if (v___x_1753_ == 0)
{
v___y_1735_ = v_fileName_1744_;
v___y_1736_ = v_fileMap_1745_;
v___y_1737_ = v_suppressElabErrors_1748_;
v___y_1738_ = v___f_1751_;
v___y_1739_ = v_ref_1747_;
v___y_1740_ = v___y_1743_;
v___y_1741_ = v___x_1753_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = l_Lean_warningAsError;
v___x_1755_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_1746_, v___x_1754_);
v___y_1735_ = v_fileName_1744_;
v___y_1736_ = v_fileMap_1745_;
v___y_1737_ = v_suppressElabErrors_1748_;
v___y_1738_ = v___f_1751_;
v___y_1739_ = v_ref_1747_;
v___y_1740_ = v___y_1743_;
v___y_1741_ = v___x_1755_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_msgData_1639_);
v___x_1756_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___boxed(lean_object* v_ref_1760_, lean_object* v_msgData_1761_, lean_object* v_severity_1762_, lean_object* v_isSilent_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v_severity_boxed_1769_; uint8_t v_isSilent_boxed_1770_; lean_object* v_res_1771_; 
v_severity_boxed_1769_ = lean_unbox(v_severity_1762_);
v_isSilent_boxed_1770_ = lean_unbox(v_isSilent_1763_);
v_res_1771_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1760_, v_msgData_1761_, v_severity_boxed_1769_, v_isSilent_boxed_1770_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v_ref_1760_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(lean_object* v_msgData_1772_, uint8_t v_severity_1773_, uint8_t v_isSilent_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_ref_1780_; lean_object* v___x_1781_; 
v_ref_1780_ = lean_ctor_get(v___y_1777_, 5);
v___x_1781_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1780_, v_msgData_1772_, v_severity_1773_, v_isSilent_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32___boxed(lean_object* v_msgData_1782_, lean_object* v_severity_1783_, lean_object* v_isSilent_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_severity_boxed_1790_; uint8_t v_isSilent_boxed_1791_; lean_object* v_res_1792_; 
v_severity_boxed_1790_ = lean_unbox(v_severity_1783_);
v_isSilent_boxed_1791_ = lean_unbox(v_isSilent_1784_);
v_res_1792_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1782_, v_severity_boxed_1790_, v_isSilent_boxed_1791_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(lean_object* v_msgData_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = 1;
v___x_1800_ = 0;
v___x_1801_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1793_, v___x_1799_, v___x_1800_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31___boxed(lean_object* v_msgData_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v_msgData_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(lean_object* v_opt_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_options_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_options_1812_ = lean_ctor_get(v___y_1810_, 2);
v___x_1813_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_1812_, v_opt_1809_);
v___x_1814_ = lean_box(v___x_1813_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg___boxed(lean_object* v_opt_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_1817_, v___y_1818_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_opt_1817_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0));
v___x_1823_ = l_Lean_stringToMessageData(v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2));
v___x_1826_ = l_Lean_stringToMessageData(v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(lean_object* v_id_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v_env_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1857_; 
v___x_1833_ = lean_st_ref_get(v___y_1831_);
v_env_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc_ref(v_env_1834_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1836_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v___x_1835_, v___y_1830_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1857_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1857_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint8_t v_isExporting_1846_; 
v_isExporting_1846_ = lean_ctor_get_uint8(v_env_1834_, sizeof(void*)*8);
lean_dec_ref(v_env_1834_);
if (v_isExporting_1846_ == 0)
{
lean_dec(v_a_1837_);
lean_dec(v_id_1827_);
goto v___jp_1841_;
}
else
{
lean_object* v_val_1847_; uint8_t v___x_1848_; 
v_val_1847_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_val_1847_);
lean_dec(v_a_1837_);
v___x_1848_ = l_Lean_isPrivateName(v_id_1827_);
if (v___x_1848_ == 0)
{
lean_dec(v_val_1847_);
lean_dec(v_id_1827_);
goto v___jp_1841_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_unbox(v_val_1847_);
lean_dec(v_val_1847_);
if (v___x_1849_ == 0)
{
lean_dec(v_id_1827_);
goto v___jp_1841_;
}
else
{
lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1839_);
v___x_1850_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_1851_ = 0;
v___x_1852_ = l_Lean_MessageData_ofConstName(v_id_1827_, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1850_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v___x_1855_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1856_;
}
}
}
v___jp_1841_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___boxed(lean_object* v_id_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_id_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(lean_object* v_id_1865_, uint8_t v_enableLog_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_env_1873_; lean_object* v_options_1874_; lean_object* v_currNamespace_1875_; lean_object* v_openDecls_1876_; lean_object* v___x_1877_; lean_object* v_env_1878_; lean_object* v_res_1879_; 
v___x_1872_ = lean_st_ref_get(v___y_1870_);
v_env_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_env_1873_);
lean_dec(v___x_1872_);
v_options_1874_ = lean_ctor_get(v___y_1869_, 2);
v_currNamespace_1875_ = lean_ctor_get(v___y_1869_, 6);
v_openDecls_1876_ = lean_ctor_get(v___y_1869_, 7);
v___x_1877_ = lean_st_ref_get(v___y_1870_);
v_env_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc_ref(v_env_1878_);
lean_dec(v___x_1877_);
lean_inc(v_openDecls_1876_);
lean_inc(v_currNamespace_1875_);
v_res_1879_ = l_Lean_ResolveName_resolveGlobalName(v_env_1873_, v_options_1874_, v_currNamespace_1875_, v_openDecls_1876_, v_id_1865_);
if (v_enableLog_1866_ == 0)
{
lean_dec_ref(v_env_1878_);
goto v___jp_1880_;
}
else
{
uint8_t v_isExporting_1883_; 
v_isExporting_1883_ = lean_ctor_get_uint8(v_env_1878_, sizeof(void*)*8);
lean_dec_ref(v_env_1878_);
if (v_isExporting_1883_ == 0)
{
goto v___jp_1880_;
}
else
{
lean_object* v___x_1884_; 
v___x_1884_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_1879_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v_fst_1886_; lean_object* v___x_1887_; 
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_fst_1886_ = lean_ctor_get(v_val_1885_, 0);
lean_inc(v_fst_1886_);
lean_dec(v_val_1885_);
v___x_1887_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_fst_1886_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1896_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
if (lean_obj_tag(v_a_1888_) == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec(v_res_1879_);
v___x_1892_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
else
{
lean_dec_ref_known(v_a_1888_, 1);
lean_del_object(v___x_1890_);
goto v___jp_1880_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_res_1879_);
v_a_1897_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1887_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1887_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_dec(v___x_1884_);
goto v___jp_1880_;
}
}
}
v___jp_1880_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_res_1879_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24___boxed(lean_object* v_id_1905_, lean_object* v_enableLog_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_enableLog_boxed_1912_; lean_object* v_res_1913_; 
v_enableLog_boxed_1912_ = lean_unbox(v_enableLog_1906_);
v_res_1913_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v_id_1905_, v_enableLog_boxed_1912_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(lean_object* v_n_u2080_1918_, lean_object* v_filter_1919_, lean_object* v_view_x3f_1920_, lean_object* v_n_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1997_; 
if (lean_obj_tag(v_view_x3f_1920_) == 1)
{
lean_object* v_val_2024_; lean_object* v_imported_2025_; lean_object* v_ctx_2026_; lean_object* v_scopes_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2035_; 
v_val_2024_ = lean_ctor_get(v_view_x3f_1920_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v_view_x3f_1920_, 1);
v_imported_2025_ = lean_ctor_get(v_val_2024_, 1);
v_ctx_2026_ = lean_ctor_get(v_val_2024_, 2);
v_scopes_2027_ = lean_ctor_get(v_val_2024_, 3);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_val_2024_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_val_2024_, 0);
lean_dec(v_unused_2036_);
v___x_2029_ = v_val_2024_;
v_isShared_2030_ = v_isSharedCheck_2035_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_scopes_2027_);
lean_inc(v_ctx_2026_);
lean_inc(v_imported_2025_);
lean_dec(v_val_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2035_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v_n_1921_);
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_n_1921_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_imported_2025_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_ctx_2026_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_scopes_2027_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_MacroScopesView_review(v___x_2032_);
v___y_1997_ = v___x_2033_;
goto v___jp_1996_;
}
}
}
else
{
lean_dec(v_view_x3f_1920_);
v___y_1997_ = v_n_1921_;
goto v___jp_1996_;
}
v___jp_1927_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
v___jp_1930_:
{
lean_object* v___x_1933_; 
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
v___x_1933_ = lean_apply_5(v___y_1932_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, lean_box(0));
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1953_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1953_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1953_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
if (lean_obj_tag(v_a_1934_) == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v___y_1931_);
v___x_1938_ = lean_box(0);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
else
{
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1934_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_a_1934_, 0);
lean_dec(v_unused_1952_);
v___x_1943_ = v_a_1934_;
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v_a_1934_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___y_1931_);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___y_1931_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1946_);
v___x_1948_ = v___x_1936_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v___y_1931_);
v_a_1954_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1933_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1933_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1965_; 
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
v___x_1965_ = lean_apply_5(v___y_1964_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, lean_box(0));
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1987_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1987_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1987_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
if (lean_obj_tag(v_a_1966_) == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec(v___y_1963_);
lean_dec_ref(v_filter_1919_);
v___x_1970_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v_a_1966_, 1);
lean_del_object(v___x_1968_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc(v___y_1963_);
v___x_1974_ = lean_apply_6(v_filter_1919_, v___y_1963_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, lean_box(0));
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; uint8_t v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___f_1977_; 
v___f_1977_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1931_ = v___y_1963_;
v___y_1932_ = v___f_1977_;
goto v___jp_1930_;
}
else
{
lean_object* v___f_1978_; 
v___f_1978_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1931_ = v___y_1963_;
v___y_1932_ = v___f_1978_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v___y_1963_);
v_a_1979_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1974_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1974_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v___y_1963_);
lean_dec_ref(v_filter_1919_);
v_a_1988_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1965_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1965_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
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
v___jp_1996_:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = 0;
lean_inc(v___y_1997_);
v___x_1999_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v___y_1997_, v___x_1998_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2015_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2015_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2015_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec(v___y_1997_);
lean_dec_ref(v_filter_1919_);
v___x_2004_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v_val_2008_; 
lean_del_object(v___x_2002_);
v_val_2008_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_a_2000_, 1);
if (lean_obj_tag(v_val_2008_) == 1)
{
lean_object* v_head_2009_; lean_object* v_tail_2010_; 
v_head_2009_ = lean_ctor_get(v_val_2008_, 0);
lean_inc(v_head_2009_);
v_tail_2010_ = lean_ctor_get(v_val_2008_, 1);
lean_inc(v_tail_2010_);
lean_dec_ref_known(v_val_2008_, 2);
if (lean_obj_tag(v_tail_2010_) == 0)
{
lean_object* v_fst_2011_; uint8_t v___x_2012_; 
v_fst_2011_ = lean_ctor_get(v_head_2009_, 0);
lean_inc(v_fst_2011_);
lean_dec(v_head_2009_);
v___x_2012_ = lean_name_eq(v_fst_2011_, v_n_u2080_1918_);
lean_dec(v_fst_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___f_2013_; 
v___f_2013_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___f_2013_;
goto v___jp_1962_;
}
else
{
lean_object* v___f_2014_; 
v___f_2014_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___f_2014_;
goto v___jp_1962_;
}
}
else
{
lean_dec(v_tail_2010_);
lean_dec(v_head_2009_);
lean_dec(v___y_1997_);
lean_dec_ref(v_filter_1919_);
goto v___jp_1927_;
}
}
else
{
lean_dec(v_val_2008_);
lean_dec(v___y_1997_);
lean_dec_ref(v_filter_1919_);
goto v___jp_1927_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v___y_1997_);
lean_dec_ref(v_filter_1919_);
v_a_2016_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1999_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1999_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___boxed(lean_object* v_n_u2080_2037_, lean_object* v_filter_2038_, lean_object* v_view_x3f_2039_, lean_object* v_n_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2037_, v_filter_2038_, v_view_x3f_2039_, v_n_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_n_u2080_2037_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(lean_object* v_n_u2080_2047_, lean_object* v_filter_2048_, lean_object* v_view_x3f_2049_, lean_object* v_as_x27_2050_, lean_object* v_b_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
if (lean_obj_tag(v_as_x27_2050_) == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_view_x3f_2049_);
lean_dec_ref(v_filter_2048_);
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_b_2051_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
else
{
lean_object* v_head_2059_; lean_object* v_tail_2060_; lean_object* v_snd_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2099_; 
v_head_2059_ = lean_ctor_get(v_as_x27_2050_, 0);
v_tail_2060_ = lean_ctor_get(v_as_x27_2050_, 1);
v_snd_2061_ = lean_ctor_get(v_b_2051_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_b_2051_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_b_2051_, 0);
lean_dec(v_unused_2100_);
v___x_2063_ = v_b_2051_;
v_isShared_2064_ = v_isSharedCheck_2099_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_snd_2061_);
lean_dec(v_b_2051_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2099_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = l_Lean_Name_appendCore(v_head_2059_, v_snd_2061_);
lean_inc(v___x_2065_);
lean_inc(v_view_x3f_2049_);
lean_inc_ref(v_filter_2048_);
v___x_2066_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2047_, v_filter_2048_, v_view_x3f_2049_, v___x_2065_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2090_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_del_object(v___x_2069_);
v___x_2071_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
lean_ctor_set(v___x_2063_, 0, v___x_2071_);
v___x_2073_ = v___x_2063_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2065_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
v_as_x27_2050_ = v_tail_2060_;
v_b_2051_ = v___x_2073_;
goto _start;
}
}
else
{
lean_object* v___x_2077_; 
lean_dec(v_view_x3f_2049_);
lean_dec_ref(v_filter_2048_);
lean_inc_ref(v_a_2067_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
lean_ctor_set(v___x_2063_, 0, v_a_2067_);
v___x_2077_ = v___x_2063_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2067_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2065_);
v___x_2077_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_a_2067_, 0);
lean_dec(v_unused_2088_);
v___x_2079_ = v_a_2067_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v_a_2067_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2077_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2082_);
v___x_2084_ = v___x_2069_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___x_2065_);
lean_del_object(v___x_2063_);
lean_dec(v_view_x3f_2049_);
lean_dec_ref(v_filter_2048_);
v_a_2091_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2066_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2066_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg___boxed(lean_object* v_n_u2080_2101_, lean_object* v_filter_2102_, lean_object* v_view_x3f_2103_, lean_object* v_as_x27_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_2101_, v_filter_2102_, v_view_x3f_2103_, v_as_x27_2104_, v_b_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_as_x27_2104_);
lean_dec(v_n_u2080_2101_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(lean_object* v_n_u2080_2115_, lean_object* v_filter_2116_, lean_object* v_view_x3f_2117_, lean_object* v_n_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___y_2125_; uint8_t v___x_2166_; 
v___x_2166_ = l_Lean_Name_hasMacroScopes(v_n_2118_);
if (v___x_2166_ == 0)
{
lean_object* v___f_2167_; 
v___f_2167_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_2125_ = v___f_2167_;
goto v___jp_2124_;
}
else
{
lean_object* v___f_2168_; 
v___f_2168_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_2125_ = v___f_2168_;
goto v___jp_2124_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; 
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
v___x_2126_ = lean_apply_5(v___y_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, lean_box(0));
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2157_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2157_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2157_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec(v_n_2118_);
lean_dec(v_view_x3f_2117_);
lean_dec_ref(v_filter_2116_);
v___x_2131_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref_known(v_a_2127_, 1);
lean_del_object(v___x_2129_);
v___x_2135_ = l_Lean_privateToUserName(v_n_2118_);
v___x_2136_ = l_Lean_Name_componentsRev(v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0));
v___x_2138_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_2115_, v_filter_2116_, v_view_x3f_2117_, v___x_2136_, v___x_2137_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___x_2136_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2148_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2148_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2148_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_val_2143_; lean_object* v_fst_2144_; lean_object* v___x_2146_; 
v_val_2143_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_val_2143_);
lean_dec(v_a_2139_);
v_fst_2144_ = lean_ctor_get(v_val_2143_, 0);
lean_inc(v_fst_2144_);
lean_dec(v_val_2143_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_fst_2144_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_fst_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_a_2149_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2138_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2138_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_n_2118_);
lean_dec(v_view_x3f_2117_);
lean_dec_ref(v_filter_2116_);
v_a_2158_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2126_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2126_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___boxed(lean_object* v_n_u2080_2169_, lean_object* v_filter_2170_, lean_object* v_view_x3f_2171_, lean_object* v_n_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2169_, v_filter_2170_, v_view_x3f_2171_, v_n_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v_n_u2080_2169_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(lean_object* v_n_u2080_2179_, lean_object* v_filter_2180_, lean_object* v_as_2181_, lean_object* v_i_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_array_get_size(v_as_2181_);
v___x_2189_ = lean_nat_dec_lt(v_i_2182_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_i_2182_);
lean_dec_ref(v_filter_2180_);
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_array_fget_borrowed(v_as_2181_, v_i_2182_);
lean_inc(v___x_2193_);
lean_inc_ref(v_filter_2180_);
v___x_2194_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2179_, v_filter_2180_, v___x_2192_, v___x_2193_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
if (lean_obj_tag(v_a_2195_) == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_add(v_i_2182_, v___x_2196_);
lean_dec(v_i_2182_);
v_i_2182_ = v___x_2197_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_2195_, 1);
lean_dec(v_i_2182_);
lean_dec_ref(v_filter_2180_);
return v___x_2194_;
}
}
else
{
lean_dec(v_i_2182_);
lean_dec_ref(v_filter_2180_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14___boxed(lean_object* v_n_u2080_2199_, lean_object* v_filter_2200_, lean_object* v_as_2201_, lean_object* v_i_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2199_, v_filter_2200_, v_as_2201_, v_i_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_as_2201_);
lean_dec(v_n_u2080_2199_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(lean_object* v_n_u2081_2209_, lean_object* v_as_2210_, size_t v_i_2211_, size_t v_stop_2212_, lean_object* v_b_2213_){
_start:
{
lean_object* v___y_2215_; uint8_t v___x_2219_; 
v___x_2219_ = lean_usize_dec_eq(v_i_2211_, v_stop_2212_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2220_ = lean_array_uget_borrowed(v_as_2210_, v_i_2211_);
v___x_2221_ = l_Lean_Name_getPrefix(v___x_2220_);
v___x_2222_ = l_Lean_Name_getPrefix(v_n_u2081_2209_);
v___x_2223_ = l_Lean_Name_isPrefixOf(v___x_2221_, v___x_2222_);
lean_dec(v___x_2222_);
lean_dec(v___x_2221_);
if (v___x_2223_ == 0)
{
v___y_2215_ = v_b_2213_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2224_; 
lean_inc(v___x_2220_);
v___x_2224_ = lean_array_push(v_b_2213_, v___x_2220_);
v___y_2215_ = v___x_2224_;
goto v___jp_2214_;
}
}
else
{
return v_b_2213_;
}
v___jp_2214_:
{
size_t v___x_2216_; size_t v___x_2217_; 
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_add(v_i_2211_, v___x_2216_);
v_i_2211_ = v___x_2217_;
v_b_2213_ = v___y_2215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15___boxed(lean_object* v_n_u2081_2225_, lean_object* v_as_2226_, lean_object* v_i_2227_, lean_object* v_stop_2228_, lean_object* v_b_2229_){
_start:
{
size_t v_i_boxed_2230_; size_t v_stop_boxed_2231_; lean_object* v_res_2232_; 
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_stop_boxed_2231_ = lean_unbox_usize(v_stop_2228_);
lean_dec(v_stop_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2225_, v_as_2226_, v_i_boxed_2230_, v_stop_boxed_2231_, v_b_2229_);
lean_dec_ref(v_as_2226_);
lean_dec(v_n_u2081_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(lean_object* v_n_u2080_2235_, uint8_t v_fullNames_2236_, uint8_t v_allowHorizAliases_2237_, lean_object* v_filter_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_view_2244_; lean_object* v_name_2245_; lean_object* v_n_u2081_2246_; 
lean_inc(v_n_u2080_2235_);
v_view_2244_ = l_Lean_extractMacroScopes(v_n_u2080_2235_);
v_name_2245_ = lean_ctor_get(v_view_2244_, 0);
lean_inc(v_name_2245_);
v_n_u2081_2246_ = l_Lean_privateToUserName(v_name_2245_);
if (v_fullNames_2236_ == 0)
{
lean_object* v___x_2247_; lean_object* v_aliases_2249_; lean_object* v_env_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2247_ = lean_st_ref_get(v___y_2242_);
v_env_2264_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_env_2264_);
lean_dec(v___x_2247_);
lean_inc(v_n_u2080_2235_);
v___x_2265_ = l_Lean_getRevAliases(v_env_2264_, v_n_u2080_2235_);
v___x_2266_ = lean_array_mk(v___x_2265_);
if (v_allowHorizAliases_2237_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_array_get_size(v___x_2266_);
v___x_2269_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0));
v___x_2270_ = lean_nat_dec_lt(v___x_2267_, v___x_2268_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v___x_2266_);
v_aliases_2249_ = v___x_2269_;
goto v___jp_2248_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2268_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2246_, v___x_2266_, v___x_2271_, v___x_2272_, v___x_2269_);
lean_dec_ref(v___x_2266_);
v_aliases_2249_ = v___x_2273_;
goto v___jp_2248_;
}
}
else
{
v_aliases_2249_ = v___x_2266_;
goto v___jp_2248_;
}
v___jp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_2238_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2235_, v_filter_2238_, v_aliases_2249_, v___x_2250_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec_ref(v_aliases_2249_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
if (lean_obj_tag(v_a_2252_) == 0)
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2262_; 
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v___x_2251_, 0);
lean_dec(v_unused_2263_);
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 1);
lean_ctor_set(v___x_2254_, 0, v_view_2244_);
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_view_2244_);
v___x_2257_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_rootNamespace;
v___x_2259_ = l_Lean_Name_append(v___x_2258_, v_n_u2081_2246_);
v___x_2260_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2235_, v_filter_2238_, v___x_2257_, v___x_2259_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v_n_u2080_2235_);
return v___x_2260_;
}
}
}
else
{
lean_dec_ref_known(v_a_2252_, 1);
lean_dec(v_n_u2081_2246_);
lean_dec_ref(v_view_2244_);
lean_dec_ref(v_filter_2238_);
lean_dec(v_n_u2080_2235_);
return v___x_2251_;
}
}
else
{
lean_dec(v_n_u2081_2246_);
lean_dec_ref(v_view_2244_);
lean_dec_ref(v_filter_2238_);
lean_dec(v_n_u2080_2235_);
return v___x_2251_;
}
}
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_view_2244_);
lean_inc(v_n_u2081_2246_);
lean_inc_ref(v___x_2274_);
lean_inc_ref(v_filter_2238_);
v___x_2275_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2235_, v_filter_2238_, v___x_2274_, v_n_u2081_2246_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
if (lean_obj_tag(v_a_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref_known(v___x_2275_, 1);
v___x_2277_ = l_Lean_rootNamespace;
v___x_2278_ = l_Lean_Name_append(v___x_2277_, v_n_u2081_2246_);
v___x_2279_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2235_, v_filter_2238_, v___x_2274_, v___x_2278_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v_n_u2080_2235_);
return v___x_2279_;
}
else
{
lean_dec_ref_known(v_a_2276_, 1);
lean_dec_ref_known(v___x_2274_, 1);
lean_dec(v_n_u2081_2246_);
lean_dec_ref(v_filter_2238_);
lean_dec(v_n_u2080_2235_);
return v___x_2275_;
}
}
else
{
lean_dec_ref_known(v___x_2274_, 1);
lean_dec(v_n_u2081_2246_);
lean_dec_ref(v_filter_2238_);
lean_dec(v_n_u2080_2235_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___boxed(lean_object* v_n_u2080_2280_, lean_object* v_fullNames_2281_, lean_object* v_allowHorizAliases_2282_, lean_object* v_filter_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v_fullNames_boxed_2289_; uint8_t v_allowHorizAliases_boxed_2290_; lean_object* v_res_2291_; 
v_fullNames_boxed_2289_ = lean_unbox(v_fullNames_2281_);
v_allowHorizAliases_boxed_2290_ = lean_unbox(v_allowHorizAliases_2282_);
v_res_2291_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2280_, v_fullNames_boxed_2289_, v_allowHorizAliases_boxed_2290_, v_filter_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
if (lean_obj_tag(v_a_2292_) == 0)
{
lean_object* v___x_2294_; 
v___x_2294_ = l_List_reverse___redArg(v_a_2293_);
return v___x_2294_;
}
else
{
lean_object* v_head_2295_; lean_object* v_tail_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2307_; 
v_head_2295_ = lean_ctor_get(v_a_2292_, 0);
v_tail_2296_ = lean_ctor_get(v_a_2292_, 1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2298_ = v_a_2292_;
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_tail_2296_);
lean_inc(v_head_2295_);
lean_dec(v_a_2292_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_snd_2300_; uint8_t v___x_2301_; 
v_snd_2300_ = lean_ctor_get(v_head_2295_, 1);
v___x_2301_ = l_List_isEmpty___redArg(v_snd_2300_);
if (v___x_2301_ == 0)
{
lean_del_object(v___x_2298_);
lean_dec(v_head_2295_);
v_a_2292_ = v_tail_2296_;
goto _start;
}
else
{
lean_object* v___x_2304_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_a_2293_);
v___x_2304_ = v___x_2298_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_head_2295_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_a_2293_);
v___x_2304_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
v_a_2292_ = v_tail_2296_;
v_a_2293_ = v___x_2304_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_opt_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_options_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_options_2311_ = lean_ctor_get(v___y_2309_, 2);
v___x_2312_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_2311_, v_opt_2308_);
v___x_2313_ = lean_box(v___x_2312_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_opt_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_2315_, v___y_2316_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_opt_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(lean_object* v_ref_2319_, lean_object* v_msgData_2320_, uint8_t v_severity_2321_, uint8_t v_isSilent_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___y_2329_; lean_object* v___y_2330_; uint8_t v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2365_; uint8_t v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2401_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; uint8_t v___y_2407_; uint8_t v___x_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; uint8_t v___y_2418_; uint8_t v___y_2419_; uint8_t v___y_2420_; uint8_t v___y_2422_; uint8_t v___x_2437_; 
v___x_2412_ = 2;
v___x_2437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2321_, v___x_2412_);
if (v___x_2437_ == 0)
{
v___y_2422_ = v___x_2437_;
goto v___jp_2421_;
}
else
{
uint8_t v___x_2438_; 
lean_inc_ref(v_msgData_2320_);
v___x_2438_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2320_);
v___y_2422_ = v___x_2438_;
goto v___jp_2421_;
}
v___jp_2328_:
{
lean_object* v___x_2338_; lean_object* v_currNamespace_2339_; lean_object* v_openDecls_2340_; lean_object* v_env_2341_; lean_object* v_nextMacroScope_2342_; lean_object* v_ngen_2343_; lean_object* v_auxDeclNGen_2344_; lean_object* v_traceState_2345_; lean_object* v_cache_2346_; lean_object* v_messages_2347_; lean_object* v_infoState_2348_; lean_object* v_snapshotTasks_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2363_; 
v___x_2338_ = lean_st_ref_take(v___y_2337_);
v_currNamespace_2339_ = lean_ctor_get(v___y_2336_, 6);
v_openDecls_2340_ = lean_ctor_get(v___y_2336_, 7);
v_env_2341_ = lean_ctor_get(v___x_2338_, 0);
v_nextMacroScope_2342_ = lean_ctor_get(v___x_2338_, 1);
v_ngen_2343_ = lean_ctor_get(v___x_2338_, 2);
v_auxDeclNGen_2344_ = lean_ctor_get(v___x_2338_, 3);
v_traceState_2345_ = lean_ctor_get(v___x_2338_, 4);
v_cache_2346_ = lean_ctor_get(v___x_2338_, 5);
v_messages_2347_ = lean_ctor_get(v___x_2338_, 6);
v_infoState_2348_ = lean_ctor_get(v___x_2338_, 7);
v_snapshotTasks_2349_ = lean_ctor_get(v___x_2338_, 8);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2351_ = v___x_2338_;
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snapshotTasks_2349_);
lean_inc(v_infoState_2348_);
lean_inc(v_messages_2347_);
lean_inc(v_cache_2346_);
lean_inc(v_traceState_2345_);
lean_inc(v_auxDeclNGen_2344_);
lean_inc(v_ngen_2343_);
lean_inc(v_nextMacroScope_2342_);
lean_inc(v_env_2341_);
lean_dec(v___x_2338_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
lean_inc(v_openDecls_2340_);
lean_inc(v_currNamespace_2339_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_currNamespace_2339_);
lean_ctor_set(v___x_2353_, 1, v_openDecls_2340_);
v___x_2354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___y_2335_);
lean_inc_ref(v___y_2333_);
lean_inc_ref(v___y_2332_);
v___x_2355_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2355_, 0, v___y_2332_);
lean_ctor_set(v___x_2355_, 1, v___y_2330_);
lean_ctor_set(v___x_2355_, 2, v___y_2334_);
lean_ctor_set(v___x_2355_, 3, v___y_2333_);
lean_ctor_set(v___x_2355_, 4, v___x_2354_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*5, v___y_2329_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*5 + 1, v___y_2331_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*5 + 2, v_isSilent_2322_);
v___x_2356_ = l_Lean_MessageLog_add(v___x_2355_, v_messages_2347_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 6, v___x_2356_);
v___x_2358_ = v___x_2351_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_env_2341_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_nextMacroScope_2342_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_ngen_2343_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_auxDeclNGen_2344_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_traceState_2345_);
lean_ctor_set(v_reuseFailAlloc_2362_, 5, v_cache_2346_);
lean_ctor_set(v_reuseFailAlloc_2362_, 6, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2362_, 7, v_infoState_2348_);
lean_ctor_set(v_reuseFailAlloc_2362_, 8, v_snapshotTasks_2349_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_st_ref_put(v___y_2337_, v___x_2358_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
v___jp_2364_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2388_; 
v___x_2373_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2320_);
v___x_2374_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_2373_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_inc_ref_n(v___y_2368_, 2);
v___x_2379_ = l_Lean_FileMap_toPosition(v___y_2368_, v___y_2367_);
lean_dec(v___y_2367_);
v___x_2380_ = l_Lean_FileMap_toPosition(v___y_2368_, v___y_2372_);
lean_dec(v___y_2372_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
v___x_2382_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
if (v___y_2371_ == 0)
{
lean_del_object(v___x_2377_);
lean_dec_ref(v___y_2365_);
v___y_2329_ = v___y_2366_;
v___y_2330_ = v___x_2379_;
v___y_2331_ = v___y_2369_;
v___y_2332_ = v___y_2370_;
v___y_2333_ = v___x_2382_;
v___y_2334_ = v___x_2381_;
v___y_2335_ = v_a_2375_;
v___y_2336_ = v___y_2325_;
v___y_2337_ = v___y_2326_;
goto v___jp_2328_;
}
else
{
uint8_t v___x_2383_; 
lean_inc(v_a_2375_);
v___x_2383_ = l_Lean_MessageData_hasTag(v___y_2365_, v_a_2375_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
lean_dec_ref_known(v___x_2381_, 1);
lean_dec_ref(v___x_2379_);
lean_dec(v_a_2375_);
v___x_2384_ = lean_box(0);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2384_);
v___x_2386_ = v___x_2377_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
else
{
lean_del_object(v___x_2377_);
v___y_2329_ = v___y_2366_;
v___y_2330_ = v___x_2379_;
v___y_2331_ = v___y_2369_;
v___y_2332_ = v___y_2370_;
v___y_2333_ = v___x_2382_;
v___y_2334_ = v___x_2381_;
v___y_2335_ = v_a_2375_;
v___y_2336_ = v___y_2325_;
v___y_2337_ = v___y_2326_;
goto v___jp_2328_;
}
}
}
}
v___jp_2389_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Syntax_getTailPos_x3f(v___y_2392_, v___y_2391_);
lean_dec(v___y_2392_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_inc(v___y_2397_);
v___y_2365_ = v___y_2390_;
v___y_2366_ = v___y_2391_;
v___y_2367_ = v___y_2397_;
v___y_2368_ = v___y_2393_;
v___y_2369_ = v___y_2394_;
v___y_2370_ = v___y_2395_;
v___y_2371_ = v___y_2396_;
v___y_2372_ = v___y_2397_;
goto v___jp_2364_;
}
else
{
lean_object* v_val_2399_; 
v_val_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_val_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___y_2365_ = v___y_2390_;
v___y_2366_ = v___y_2391_;
v___y_2367_ = v___y_2397_;
v___y_2368_ = v___y_2393_;
v___y_2369_ = v___y_2394_;
v___y_2370_ = v___y_2395_;
v___y_2371_ = v___y_2396_;
v___y_2372_ = v_val_2399_;
goto v___jp_2364_;
}
}
v___jp_2400_:
{
lean_object* v_ref_2408_; lean_object* v___x_2409_; 
v_ref_2408_ = l_Lean_replaceRef(v_ref_2319_, v___y_2404_);
v___x_2409_ = l_Lean_Syntax_getPos_x3f(v_ref_2408_, v___y_2402_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___y_2390_ = v___y_2401_;
v___y_2391_ = v___y_2402_;
v___y_2392_ = v_ref_2408_;
v___y_2393_ = v___y_2403_;
v___y_2394_ = v___y_2407_;
v___y_2395_ = v___y_2405_;
v___y_2396_ = v___y_2406_;
v___y_2397_ = v___x_2410_;
goto v___jp_2389_;
}
else
{
lean_object* v_val_2411_; 
v_val_2411_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_val_2411_);
lean_dec_ref_known(v___x_2409_, 1);
v___y_2390_ = v___y_2401_;
v___y_2391_ = v___y_2402_;
v___y_2392_ = v_ref_2408_;
v___y_2393_ = v___y_2403_;
v___y_2394_ = v___y_2407_;
v___y_2395_ = v___y_2405_;
v___y_2396_ = v___y_2406_;
v___y_2397_ = v_val_2411_;
goto v___jp_2389_;
}
}
v___jp_2413_:
{
if (v___y_2420_ == 0)
{
v___y_2401_ = v___y_2414_;
v___y_2402_ = v___y_2419_;
v___y_2403_ = v___y_2415_;
v___y_2404_ = v___y_2416_;
v___y_2405_ = v___y_2417_;
v___y_2406_ = v___y_2418_;
v___y_2407_ = v_severity_2321_;
goto v___jp_2400_;
}
else
{
v___y_2401_ = v___y_2414_;
v___y_2402_ = v___y_2419_;
v___y_2403_ = v___y_2415_;
v___y_2404_ = v___y_2416_;
v___y_2405_ = v___y_2417_;
v___y_2406_ = v___y_2418_;
v___y_2407_ = v___x_2412_;
goto v___jp_2400_;
}
}
v___jp_2421_:
{
if (v___y_2422_ == 0)
{
lean_object* v_fileName_2423_; lean_object* v_fileMap_2424_; lean_object* v_options_2425_; lean_object* v_ref_2426_; uint8_t v_suppressElabErrors_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; uint8_t v___x_2431_; uint8_t v___x_2432_; 
v_fileName_2423_ = lean_ctor_get(v___y_2325_, 0);
v_fileMap_2424_ = lean_ctor_get(v___y_2325_, 1);
v_options_2425_ = lean_ctor_get(v___y_2325_, 2);
v_ref_2426_ = lean_ctor_get(v___y_2325_, 5);
v_suppressElabErrors_2427_ = lean_ctor_get_uint8(v___y_2325_, sizeof(void*)*14 + 1);
v___x_2428_ = lean_box(v_suppressElabErrors_2427_);
v___x_2429_ = lean_box(v___y_2422_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2430_, 0, v___x_2428_);
lean_closure_set(v___f_2430_, 1, v___x_2429_);
v___x_2431_ = 1;
v___x_2432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2321_, v___x_2431_);
if (v___x_2432_ == 0)
{
v___y_2414_ = v___f_2430_;
v___y_2415_ = v_fileMap_2424_;
v___y_2416_ = v_ref_2426_;
v___y_2417_ = v_fileName_2423_;
v___y_2418_ = v_suppressElabErrors_2427_;
v___y_2419_ = v___y_2422_;
v___y_2420_ = v___x_2432_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = l_Lean_warningAsError;
v___x_2434_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__4(v_options_2425_, v___x_2433_);
v___y_2414_ = v___f_2430_;
v___y_2415_ = v_fileMap_2424_;
v___y_2416_ = v_ref_2426_;
v___y_2417_ = v_fileName_2423_;
v___y_2418_ = v_suppressElabErrors_2427_;
v___y_2419_ = v___y_2422_;
v___y_2420_ = v___x_2434_;
goto v___jp_2413_;
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v_msgData_2320_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_ref_2439_, lean_object* v_msgData_2440_, lean_object* v_severity_2441_, lean_object* v_isSilent_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
uint8_t v_severity_boxed_2448_; uint8_t v_isSilent_boxed_2449_; lean_object* v_res_2450_; 
v_severity_boxed_2448_ = lean_unbox(v_severity_2441_);
v_isSilent_boxed_2449_ = lean_unbox(v_isSilent_2442_);
v_res_2450_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2439_, v_msgData_2440_, v_severity_boxed_2448_, v_isSilent_boxed_2449_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_ref_2439_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(lean_object* v_msgData_2451_, uint8_t v_severity_2452_, uint8_t v_isSilent_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_ref_2459_; lean_object* v___x_2460_; 
v_ref_2459_ = lean_ctor_get(v___y_2456_, 5);
v___x_2460_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2459_, v_msgData_2451_, v_severity_2452_, v_isSilent_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_2461_, lean_object* v_severity_2462_, lean_object* v_isSilent_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v_severity_boxed_2469_; uint8_t v_isSilent_boxed_2470_; lean_object* v_res_2471_; 
v_severity_boxed_2469_ = lean_unbox(v_severity_2462_);
v_isSilent_boxed_2470_ = lean_unbox(v_isSilent_2463_);
v_res_2471_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2461_, v_severity_boxed_2469_, v_isSilent_boxed_2470_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(lean_object* v_msgData_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
uint8_t v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = 1;
v___x_2479_ = 0;
v___x_2480_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2472_, v___x_2478_, v___x_2479_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v_msgData_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(lean_object* v_id_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v_env_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2517_; 
v___x_2494_ = lean_st_ref_get(v___y_2492_);
v_env_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc_ref(v_env_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_2497_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v___x_2496_, v___y_2491_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2517_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint8_t v_isExporting_2507_; 
v_isExporting_2507_ = lean_ctor_get_uint8(v_env_2495_, sizeof(void*)*8);
lean_dec_ref(v_env_2495_);
if (v_isExporting_2507_ == 0)
{
lean_dec(v_a_2498_);
lean_dec(v_id_2488_);
goto v___jp_2502_;
}
else
{
uint8_t v___x_2508_; 
v___x_2508_ = l_Lean_isPrivateName(v_id_2488_);
if (v___x_2508_ == 0)
{
lean_dec(v_a_2498_);
lean_dec(v_id_2488_);
goto v___jp_2502_;
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_unbox(v_a_2498_);
lean_dec(v_a_2498_);
if (v___x_2509_ == 0)
{
lean_dec(v_id_2488_);
goto v___jp_2502_;
}
else
{
lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_del_object(v___x_2500_);
v___x_2510_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_2511_ = 0;
v___x_2512_ = l_Lean_MessageData_ofConstName(v_id_2488_, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2510_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_2515_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2516_;
}
}
}
v___jp_2502_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(0);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1___boxed(lean_object* v_id_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_id_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_id_2525_, uint8_t v_enableLog_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v_env_2533_; lean_object* v_options_2534_; lean_object* v_currNamespace_2535_; lean_object* v_openDecls_2536_; lean_object* v___x_2537_; lean_object* v_env_2538_; lean_object* v_res_2539_; 
v___x_2532_ = lean_st_ref_get(v___y_2530_);
v_env_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_ref(v_env_2533_);
lean_dec(v___x_2532_);
v_options_2534_ = lean_ctor_get(v___y_2529_, 2);
v_currNamespace_2535_ = lean_ctor_get(v___y_2529_, 6);
v_openDecls_2536_ = lean_ctor_get(v___y_2529_, 7);
v___x_2537_ = lean_st_ref_get(v___y_2530_);
v_env_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_env_2538_);
lean_dec(v___x_2537_);
lean_inc(v_openDecls_2536_);
lean_inc(v_currNamespace_2535_);
v_res_2539_ = l_Lean_ResolveName_resolveGlobalName(v_env_2533_, v_options_2534_, v_currNamespace_2535_, v_openDecls_2536_, v_id_2525_);
if (v_enableLog_2526_ == 0)
{
lean_object* v___x_2540_; 
lean_dec_ref(v_env_2538_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_res_2539_);
return v___x_2540_;
}
else
{
uint8_t v_isExporting_2541_; 
v_isExporting_2541_ = lean_ctor_get_uint8(v_env_2538_, sizeof(void*)*8);
lean_dec_ref(v_env_2538_);
if (v_isExporting_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_res_2539_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_2539_);
if (lean_obj_tag(v___x_2543_) == 1)
{
lean_object* v_val_2544_; lean_object* v_fst_2545_; lean_object* v___x_2546_; 
v_val_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v_fst_2545_ = lean_ctor_get(v_val_2544_, 0);
lean_inc(v_fst_2545_);
lean_dec(v_val_2544_);
v___x_2546_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_fst_2545_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2554_);
v___x_2548_ = v___x_2546_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v___x_2546_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_res_2539_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_res_2539_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_res_2539_);
v_a_2555_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2546_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2546_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v___x_2563_; 
lean_dec(v___x_2543_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_res_2539_);
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_id_2564_, lean_object* v_enableLog_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v_enableLog_boxed_2571_; lean_object* v_res_2572_; 
v_enableLog_boxed_2571_ = lean_unbox(v_enableLog_2565_);
v_res_2572_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_id_2564_, v_enableLog_boxed_2571_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(lean_object* v_view_2573_, lean_object* v_findLocalDecl_x3f_2574_, lean_object* v_n_2575_, lean_object* v_projs_2576_, uint8_t v_globalDeclFound_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v_globalDeclFoundNext_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v_imported_2593_; lean_object* v_ctx_2594_; lean_object* v_scopes_2595_; lean_object* v_givenNameView_2596_; uint8_t v___y_2598_; 
v_imported_2593_ = lean_ctor_get(v_view_2573_, 1);
v_ctx_2594_ = lean_ctor_get(v_view_2573_, 2);
v_scopes_2595_ = lean_ctor_get(v_view_2573_, 3);
lean_inc(v_scopes_2595_);
lean_inc(v_ctx_2594_);
lean_inc(v_imported_2593_);
lean_inc(v_n_2575_);
v_givenNameView_2596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2596_, 0, v_n_2575_);
lean_ctor_set(v_givenNameView_2596_, 1, v_imported_2593_);
lean_ctor_set(v_givenNameView_2596_, 2, v_ctx_2594_);
lean_ctor_set(v_givenNameView_2596_, 3, v_scopes_2595_);
if (v_globalDeclFound_2577_ == 0)
{
v___y_2598_ = v_globalDeclFound_2577_;
goto v___jp_2597_;
}
else
{
uint8_t v___x_2633_; 
v___x_2633_ = l_List_isEmpty___redArg(v_projs_2576_);
if (v___x_2633_ == 0)
{
v___y_2598_ = v_globalDeclFound_2577_;
goto v___jp_2597_;
}
else
{
uint8_t v___x_2634_; 
v___x_2634_ = 0;
v___y_2598_ = v___x_2634_;
goto v___jp_2597_;
}
}
v___jp_2583_:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2584_);
lean_ctor_set(v___x_2591_, 1, v_projs_2576_);
v_n_2575_ = v___y_2585_;
v_projs_2576_ = v___x_2591_;
v_globalDeclFound_2577_ = v_globalDeclFoundNext_2586_;
v___y_2578_ = v___y_2587_;
v___y_2579_ = v___y_2588_;
v___y_2580_ = v___y_2589_;
v___y_2581_ = v___y_2590_;
goto _start;
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(v___y_2598_);
lean_inc_ref(v_findLocalDecl_x3f_2574_);
lean_inc_ref(v_givenNameView_2596_);
v___x_2600_ = lean_apply_2(v_findLocalDecl_x3f_2574_, v_givenNameView_2596_, v___x_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
if (lean_obj_tag(v_n_2575_) == 1)
{
if (v_globalDeclFound_2577_ == 0)
{
lean_object* v_pre_2601_; lean_object* v_str_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_pre_2601_ = lean_ctor_get(v_n_2575_, 0);
lean_inc(v_pre_2601_);
v_str_2602_ = lean_ctor_get(v_n_2575_, 1);
lean_inc_ref(v_str_2602_);
lean_dec_ref_known(v_n_2575_, 2);
v___x_2603_ = l_Lean_MacroScopesView_review(v_givenNameView_2596_);
v___x_2604_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v___x_2603_, v_globalDeclFound_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v_r_2607_; uint8_t v___x_2608_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_box(0);
v_r_2607_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(v_a_2605_, v___x_2606_);
v___x_2608_ = l_List_isEmpty___redArg(v_r_2607_);
lean_dec(v_r_2607_);
if (v___x_2608_ == 0)
{
uint8_t v_globalDeclFoundNext_2609_; 
v_globalDeclFoundNext_2609_ = 1;
v___y_2584_ = v_str_2602_;
v___y_2585_ = v_pre_2601_;
v_globalDeclFoundNext_2586_ = v_globalDeclFoundNext_2609_;
v___y_2587_ = v___y_2578_;
v___y_2588_ = v___y_2579_;
v___y_2589_ = v___y_2580_;
v___y_2590_ = v___y_2581_;
goto v___jp_2583_;
}
else
{
v___y_2584_ = v_str_2602_;
v___y_2585_ = v_pre_2601_;
v_globalDeclFoundNext_2586_ = v_globalDeclFound_2577_;
v___y_2587_ = v___y_2578_;
v___y_2588_ = v___y_2579_;
v___y_2589_ = v___y_2580_;
v___y_2590_ = v___y_2581_;
goto v___jp_2583_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v_str_2602_);
lean_dec(v_pre_2601_);
lean_dec(v_projs_2576_);
lean_dec_ref(v_findLocalDecl_x3f_2574_);
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
else
{
lean_object* v_pre_2618_; lean_object* v_str_2619_; 
lean_dec_ref_known(v_givenNameView_2596_, 4);
v_pre_2618_ = lean_ctor_get(v_n_2575_, 0);
lean_inc(v_pre_2618_);
v_str_2619_ = lean_ctor_get(v_n_2575_, 1);
lean_inc_ref(v_str_2619_);
lean_dec_ref_known(v_n_2575_, 2);
v___y_2584_ = v_str_2619_;
v___y_2585_ = v_pre_2618_;
v_globalDeclFoundNext_2586_ = v_globalDeclFound_2577_;
v___y_2587_ = v___y_2578_;
v___y_2588_ = v___y_2579_;
v___y_2589_ = v___y_2580_;
v___y_2590_ = v___y_2581_;
goto v___jp_2583_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref_known(v_givenNameView_2596_, 4);
lean_dec(v_projs_2576_);
lean_dec(v_n_2575_);
lean_dec_ref(v_findLocalDecl_x3f_2574_);
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v_givenNameView_2596_, 4);
lean_dec(v_n_2575_);
lean_dec_ref(v_findLocalDecl_x3f_2574_);
v_val_2622_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2624_ = v___x_2600_;
v_isShared_2625_ = v_isSharedCheck_2632_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_val_2622_);
lean_dec(v___x_2600_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2632_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = l_Lean_LocalDecl_toExpr(v_val_2622_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v_projs_2576_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2627_);
v___x_2629_ = v___x_2624_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11___boxed(lean_object* v_view_2635_, lean_object* v_findLocalDecl_x3f_2636_, lean_object* v_n_2637_, lean_object* v_projs_2638_, lean_object* v_globalDeclFound_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
uint8_t v_globalDeclFound_boxed_2645_; lean_object* v_res_2646_; 
v_globalDeclFound_boxed_2645_ = lean_unbox(v_globalDeclFound_2639_);
v_res_2646_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2635_, v_findLocalDecl_x3f_2636_, v_n_2637_, v_projs_2638_, v_globalDeclFound_boxed_2645_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v_view_2635_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(lean_object* v_localDecl_2647_, lean_object* v_givenName_2648_){
_start:
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = l_Lean_LocalDecl_userName(v_localDecl_2647_);
v___x_2650_ = lean_name_eq(v___x_2649_, v_givenName_2648_);
lean_dec(v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
lean_dec_ref(v_localDecl_2647_);
v___x_2651_ = lean_box(0);
return v___x_2651_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_localDecl_2647_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_localDecl_2653_, lean_object* v_givenName_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_localDecl_2653_, v_givenName_2654_);
lean_dec(v_givenName_2654_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(lean_object* v_t_2656_, lean_object* v_k_2657_){
_start:
{
if (lean_obj_tag(v_t_2656_) == 0)
{
lean_object* v_k_2658_; lean_object* v_v_2659_; lean_object* v_l_2660_; lean_object* v_r_2661_; uint8_t v___x_2662_; 
v_k_2658_ = lean_ctor_get(v_t_2656_, 1);
v_v_2659_ = lean_ctor_get(v_t_2656_, 2);
v_l_2660_ = lean_ctor_get(v_t_2656_, 3);
v_r_2661_ = lean_ctor_get(v_t_2656_, 4);
v___x_2662_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2657_, v_k_2658_);
switch(v___x_2662_)
{
case 0:
{
v_t_2656_ = v_l_2660_;
goto _start;
}
case 1:
{
lean_object* v___x_2664_; 
lean_inc(v_v_2659_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_v_2659_);
return v___x_2664_;
}
default: 
{
v_t_2656_ = v_r_2661_;
goto _start;
}
}
}
else
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_box(0);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_t_2667_, lean_object* v_k_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_2667_, v_k_2668_);
lean_dec(v_k_2668_);
lean_dec(v_t_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(lean_object* v_givenName_2670_, uint8_t v_skipAuxDecl_2671_, lean_object* v_auxDeclToFullName_2672_, lean_object* v___x_2673_, lean_object* v_givenNameView_2674_, lean_object* v_as_2675_, lean_object* v_i_2676_){
_start:
{
lean_object* v_zero_2677_; uint8_t v_isZero_2678_; 
v_zero_2677_ = lean_unsigned_to_nat(0u);
v_isZero_2678_ = lean_nat_dec_eq(v_i_2676_, v_zero_2677_);
if (v_isZero_2678_ == 1)
{
lean_object* v___x_2679_; 
lean_dec(v_i_2676_);
lean_dec_ref(v_givenNameView_2674_);
lean_dec(v___x_2673_);
v___x_2679_ = lean_box(0);
return v___x_2679_;
}
else
{
lean_object* v_one_2680_; lean_object* v_n_2681_; lean_object* v___y_2683_; lean_object* v___x_2685_; 
v_one_2680_ = lean_unsigned_to_nat(1u);
v_n_2681_ = lean_nat_sub(v_i_2676_, v_one_2680_);
lean_dec(v_i_2676_);
v___x_2685_ = lean_array_fget_borrowed(v_as_2675_, v_n_2681_);
if (lean_obj_tag(v___x_2685_) == 0)
{
v___y_2683_ = v___x_2685_;
goto v___jp_2682_;
}
else
{
lean_object* v_val_2686_; uint8_t v___x_2687_; 
v_val_2686_ = lean_ctor_get(v___x_2685_, 0);
v___x_2687_ = l_Lean_LocalDecl_isAuxDecl(v_val_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_inc(v_val_2686_);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2686_, v_givenName_2670_);
v___y_2683_ = v___x_2688_;
goto v___jp_2682_;
}
else
{
if (v_skipAuxDecl_2671_ == 0)
{
if (v___x_2687_ == 0)
{
v_i_2676_ = v_n_2681_;
goto _start;
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = l_Lean_LocalDecl_fvarId(v_val_2686_);
v___x_2691_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_auxDeclToFullName_2672_, v___x_2690_);
lean_dec(v___x_2690_);
if (lean_obj_tag(v___x_2691_) == 1)
{
lean_object* v_val_2692_; lean_object* v_fullDeclView_2693_; lean_object* v___y_2695_; lean_object* v_name_2716_; lean_object* v___x_2717_; 
v_val_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_val_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v_fullDeclView_2693_ = l_Lean_extractMacroScopes(v_val_2692_);
v_name_2716_ = lean_ctor_get(v_fullDeclView_2693_, 0);
lean_inc_n(v_name_2716_, 2);
v___x_2717_ = l_Lean_privateToUserName_x3f(v_name_2716_);
if (lean_obj_tag(v___x_2717_) == 0)
{
v___y_2695_ = v_name_2716_;
goto v___jp_2694_;
}
else
{
lean_object* v_val_2718_; 
lean_dec(v_name_2716_);
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___y_2695_ = v_val_2718_;
goto v___jp_2694_;
}
v___jp_2694_:
{
lean_object* v_imported_2696_; lean_object* v_ctx_2697_; lean_object* v_scopes_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2714_; 
v_imported_2696_ = lean_ctor_get(v_fullDeclView_2693_, 1);
v_ctx_2697_ = lean_ctor_get(v_fullDeclView_2693_, 2);
v_scopes_2698_ = lean_ctor_get(v_fullDeclView_2693_, 3);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_fullDeclView_2693_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_fullDeclView_2693_, 0);
lean_dec(v_unused_2715_);
v___x_2700_ = v_fullDeclView_2693_;
v_isShared_2701_ = v_isSharedCheck_2714_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_scopes_2698_);
lean_inc(v_ctx_2697_);
lean_inc(v_imported_2696_);
lean_dec(v_fullDeclView_2693_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2714_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_fullDeclView_2703_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___y_2695_);
v_fullDeclView_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___y_2695_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_imported_2696_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v_ctx_2697_);
lean_ctor_set(v_reuseFailAlloc_2713_, 3, v_scopes_2698_);
v_fullDeclView_2703_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v_fullDeclName_2704_; uint8_t v___x_2705_; 
lean_inc_ref(v_fullDeclView_2703_);
v_fullDeclName_2704_ = l_Lean_MacroScopesView_review(v_fullDeclView_2703_);
v___x_2705_ = l_Lean_Name_isPrefixOf(v___x_2673_, v_fullDeclName_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref(v_fullDeclView_2703_);
lean_inc(v___x_2673_);
lean_inc_ref(v_givenNameView_2674_);
lean_inc(v_val_2686_);
v___x_2706_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2686_, v_givenNameView_2674_, v_fullDeclName_2704_, v___x_2673_);
lean_dec(v_fullDeclName_2704_);
v___y_2683_ = v___x_2706_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2707_; lean_object* v_localDeclNameView_2708_; uint8_t v___x_2709_; 
lean_dec(v_fullDeclName_2704_);
v___x_2707_ = l_Lean_LocalDecl_userName(v_val_2686_);
v_localDeclNameView_2708_ = l_Lean_extractMacroScopes(v___x_2707_);
v___x_2709_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2708_, v_givenNameView_2674_);
lean_dec_ref(v_localDeclNameView_2708_);
if (v___x_2709_ == 0)
{
lean_dec_ref(v_fullDeclView_2703_);
v_i_2676_ = v_n_2681_;
goto _start;
}
else
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2674_, v_fullDeclView_2703_);
lean_dec_ref(v_fullDeclView_2703_);
if (v___x_2711_ == 0)
{
v_i_2676_ = v_n_2681_;
goto _start;
}
else
{
lean_inc_ref(v___x_2685_);
v___y_2683_ = v___x_2685_;
goto v___jp_2682_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2719_; 
lean_dec(v___x_2691_);
lean_inc(v_val_2686_);
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2686_, v_givenName_2670_);
v___y_2683_ = v___x_2719_;
goto v___jp_2682_;
}
}
}
else
{
v_i_2676_ = v_n_2681_;
goto _start;
}
}
}
v___jp_2682_:
{
if (lean_obj_tag(v___y_2683_) == 0)
{
v_i_2676_ = v_n_2681_;
goto _start;
}
else
{
lean_dec(v_n_2681_);
lean_dec_ref(v_givenNameView_2674_);
lean_dec(v___x_2673_);
return v___y_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___boxed(lean_object* v_givenName_2721_, lean_object* v_skipAuxDecl_2722_, lean_object* v_auxDeclToFullName_2723_, lean_object* v___x_2724_, lean_object* v_givenNameView_2725_, lean_object* v_as_2726_, lean_object* v_i_2727_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2728_; lean_object* v_res_2729_; 
v_skipAuxDecl_boxed_2728_ = lean_unbox(v_skipAuxDecl_2722_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2721_, v_skipAuxDecl_boxed_2728_, v_auxDeclToFullName_2723_, v___x_2724_, v_givenNameView_2725_, v_as_2726_, v_i_2727_);
lean_dec_ref(v_as_2726_);
lean_dec(v_auxDeclToFullName_2723_);
lean_dec(v_givenName_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(lean_object* v_givenName_2730_, uint8_t v_skipAuxDecl_2731_, lean_object* v_auxDeclToFullName_2732_, lean_object* v___x_2733_, lean_object* v_givenNameView_2734_, lean_object* v_as_2735_, lean_object* v_i_2736_){
_start:
{
lean_object* v_zero_2737_; uint8_t v_isZero_2738_; 
v_zero_2737_ = lean_unsigned_to_nat(0u);
v_isZero_2738_ = lean_nat_dec_eq(v_i_2736_, v_zero_2737_);
if (v_isZero_2738_ == 1)
{
lean_object* v___x_2739_; 
lean_dec(v_i_2736_);
lean_dec_ref(v_givenNameView_2734_);
lean_dec(v___x_2733_);
v___x_2739_ = lean_box(0);
return v___x_2739_;
}
else
{
lean_object* v_one_2740_; lean_object* v_n_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_one_2740_ = lean_unsigned_to_nat(1u);
v_n_2741_ = lean_nat_sub(v_i_2736_, v_one_2740_);
lean_dec(v_i_2736_);
v___x_2742_ = lean_array_fget_borrowed(v_as_2735_, v_n_2741_);
lean_inc_ref(v_givenNameView_2734_);
lean_inc(v___x_2733_);
v___x_2743_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2730_, v_skipAuxDecl_2731_, v_auxDeclToFullName_2732_, v___x_2733_, v_givenNameView_2734_, v___x_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
v_i_2736_ = v_n_2741_;
goto _start;
}
else
{
lean_dec(v_n_2741_);
lean_dec_ref(v_givenNameView_2734_);
lean_dec(v___x_2733_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(lean_object* v_givenName_2745_, uint8_t v_skipAuxDecl_2746_, lean_object* v_auxDeclToFullName_2747_, lean_object* v___x_2748_, lean_object* v_givenNameView_2749_, lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_cs_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_cs_2751_ = lean_ctor_get(v_x_2750_, 0);
v___x_2752_ = lean_array_get_size(v_cs_2751_);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2745_, v_skipAuxDecl_2746_, v_auxDeclToFullName_2747_, v___x_2748_, v_givenNameView_2749_, v_cs_2751_, v___x_2752_);
return v___x_2753_;
}
else
{
lean_object* v_vs_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_vs_2754_ = lean_ctor_get(v_x_2750_, 0);
v___x_2755_ = lean_array_get_size(v_vs_2754_);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2745_, v_skipAuxDecl_2746_, v_auxDeclToFullName_2747_, v___x_2748_, v_givenNameView_2749_, v_vs_2754_, v___x_2755_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_givenName_2757_, lean_object* v_skipAuxDecl_2758_, lean_object* v_auxDeclToFullName_2759_, lean_object* v___x_2760_, lean_object* v_givenNameView_2761_, lean_object* v_x_2762_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2763_; lean_object* v_res_2764_; 
v_skipAuxDecl_boxed_2763_ = lean_unbox(v_skipAuxDecl_2758_);
v_res_2764_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2757_, v_skipAuxDecl_boxed_2763_, v_auxDeclToFullName_2759_, v___x_2760_, v_givenNameView_2761_, v_x_2762_);
lean_dec_ref(v_x_2762_);
lean_dec(v_auxDeclToFullName_2759_);
lean_dec(v_givenName_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg___boxed(lean_object* v_givenName_2765_, lean_object* v_skipAuxDecl_2766_, lean_object* v_auxDeclToFullName_2767_, lean_object* v___x_2768_, lean_object* v_givenNameView_2769_, lean_object* v_as_2770_, lean_object* v_i_2771_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2772_; lean_object* v_res_2773_; 
v_skipAuxDecl_boxed_2772_ = lean_unbox(v_skipAuxDecl_2766_);
v_res_2773_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2765_, v_skipAuxDecl_boxed_2772_, v_auxDeclToFullName_2767_, v___x_2768_, v_givenNameView_2769_, v_as_2770_, v_i_2771_);
lean_dec_ref(v_as_2770_);
lean_dec(v_auxDeclToFullName_2767_);
lean_dec(v_givenName_2765_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(lean_object* v_givenName_2774_, uint8_t v_skipAuxDecl_2775_, lean_object* v_auxDeclToFullName_2776_, lean_object* v___x_2777_, lean_object* v_givenNameView_2778_, lean_object* v_t_2779_){
_start:
{
lean_object* v_root_2780_; lean_object* v_tail_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_root_2780_ = lean_ctor_get(v_t_2779_, 0);
v_tail_2781_ = lean_ctor_get(v_t_2779_, 1);
v___x_2782_ = lean_array_get_size(v_tail_2781_);
lean_inc_ref(v_givenNameView_2778_);
lean_inc(v___x_2777_);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2774_, v_skipAuxDecl_2775_, v_auxDeclToFullName_2776_, v___x_2777_, v_givenNameView_2778_, v_tail_2781_, v___x_2782_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2774_, v_skipAuxDecl_2775_, v_auxDeclToFullName_2776_, v___x_2777_, v_givenNameView_2778_, v_root_2780_);
return v___x_2784_;
}
else
{
lean_dec_ref(v_givenNameView_2778_);
lean_dec(v___x_2777_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9___boxed(lean_object* v_givenName_2785_, lean_object* v_skipAuxDecl_2786_, lean_object* v_auxDeclToFullName_2787_, lean_object* v___x_2788_, lean_object* v_givenNameView_2789_, lean_object* v_t_2790_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2791_; lean_object* v_res_2792_; 
v_skipAuxDecl_boxed_2791_ = lean_unbox(v_skipAuxDecl_2786_);
v_res_2792_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2785_, v_skipAuxDecl_boxed_2791_, v_auxDeclToFullName_2787_, v___x_2788_, v_givenNameView_2789_, v_t_2790_);
lean_dec_ref(v_t_2790_);
lean_dec(v_auxDeclToFullName_2787_);
lean_dec(v_givenName_2785_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(lean_object* v_localDecl_x3f_2793_, lean_object* v_givenName_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_){
_start:
{
lean_object* v_zero_2797_; uint8_t v_isZero_2798_; 
v_zero_2797_ = lean_unsigned_to_nat(0u);
v_isZero_2798_ = lean_nat_dec_eq(v_i_2796_, v_zero_2797_);
if (v_isZero_2798_ == 1)
{
lean_object* v___x_2799_; 
lean_dec(v_i_2796_);
v___x_2799_ = lean_box(0);
return v___x_2799_;
}
else
{
lean_object* v_one_2800_; lean_object* v_n_2801_; lean_object* v___y_2803_; lean_object* v___x_2805_; 
v_one_2800_ = lean_unsigned_to_nat(1u);
v_n_2801_ = lean_nat_sub(v_i_2796_, v_one_2800_);
lean_dec(v_i_2796_);
v___x_2805_ = lean_array_fget_borrowed(v_as_2795_, v_n_2801_);
if (lean_obj_tag(v___x_2805_) == 0)
{
v___y_2803_ = v___x_2805_;
goto v___jp_2802_;
}
else
{
lean_object* v_val_2806_; uint8_t v___x_2807_; 
v_val_2806_ = lean_ctor_get(v___x_2805_, 0);
v___x_2807_ = l_Lean_LocalDecl_isAuxDecl(v_val_2806_);
if (v___x_2807_ == 0)
{
v___y_2803_ = v_localDecl_x3f_2793_;
goto v___jp_2802_;
}
else
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = l_Lean_LocalDecl_userName(v_val_2806_);
v___x_2809_ = lean_name_eq(v___x_2808_, v_givenName_2794_);
lean_dec(v___x_2808_);
if (v___x_2809_ == 0)
{
v_i_2796_ = v_n_2801_;
goto _start;
}
else
{
v___y_2803_ = v___x_2805_;
goto v___jp_2802_;
}
}
}
v___jp_2802_:
{
if (lean_obj_tag(v___y_2803_) == 0)
{
v_i_2796_ = v_n_2801_;
goto _start;
}
else
{
lean_dec(v_n_2801_);
lean_inc_ref(v___y_2803_);
return v___y_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_localDecl_x3f_2811_, lean_object* v_givenName_2812_, lean_object* v_as_2813_, lean_object* v_i_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2811_, v_givenName_2812_, v_as_2813_, v_i_2814_);
lean_dec_ref(v_as_2813_);
lean_dec(v_givenName_2812_);
lean_dec(v_localDecl_x3f_2811_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(lean_object* v_localDecl_x3f_2816_, lean_object* v_givenName_2817_, lean_object* v_as_2818_, lean_object* v_i_2819_){
_start:
{
lean_object* v_zero_2820_; uint8_t v_isZero_2821_; 
v_zero_2820_ = lean_unsigned_to_nat(0u);
v_isZero_2821_ = lean_nat_dec_eq(v_i_2819_, v_zero_2820_);
if (v_isZero_2821_ == 1)
{
lean_object* v___x_2822_; 
lean_dec(v_i_2819_);
v___x_2822_ = lean_box(0);
return v___x_2822_;
}
else
{
lean_object* v_one_2823_; lean_object* v_n_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_one_2823_ = lean_unsigned_to_nat(1u);
v_n_2824_ = lean_nat_sub(v_i_2819_, v_one_2823_);
lean_dec(v_i_2819_);
v___x_2825_ = lean_array_fget_borrowed(v_as_2818_, v_n_2824_);
v___x_2826_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2816_, v_givenName_2817_, v___x_2825_);
if (lean_obj_tag(v___x_2826_) == 0)
{
v_i_2819_ = v_n_2824_;
goto _start;
}
else
{
lean_dec(v_n_2824_);
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(lean_object* v_localDecl_x3f_2828_, lean_object* v_givenName_2829_, lean_object* v_x_2830_){
_start:
{
if (lean_obj_tag(v_x_2830_) == 0)
{
lean_object* v_cs_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_cs_2831_ = lean_ctor_get(v_x_2830_, 0);
v___x_2832_ = lean_array_get_size(v_cs_2831_);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2828_, v_givenName_2829_, v_cs_2831_, v___x_2832_);
return v___x_2833_;
}
else
{
lean_object* v_vs_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_vs_2834_ = lean_ctor_get(v_x_2830_, 0);
v___x_2835_ = lean_array_get_size(v_vs_2834_);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2828_, v_givenName_2829_, v_vs_2834_, v___x_2835_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15___boxed(lean_object* v_localDecl_x3f_2837_, lean_object* v_givenName_2838_, lean_object* v_x_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2837_, v_givenName_2838_, v_x_2839_);
lean_dec_ref(v_x_2839_);
lean_dec(v_givenName_2838_);
lean_dec(v_localDecl_x3f_2837_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg___boxed(lean_object* v_localDecl_x3f_2841_, lean_object* v_givenName_2842_, lean_object* v_as_2843_, lean_object* v_i_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2841_, v_givenName_2842_, v_as_2843_, v_i_2844_);
lean_dec_ref(v_as_2843_);
lean_dec(v_givenName_2842_);
lean_dec(v_localDecl_x3f_2841_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(lean_object* v_localDecl_x3f_2846_, lean_object* v_givenName_2847_, lean_object* v_t_2848_){
_start:
{
lean_object* v_root_2849_; lean_object* v_tail_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_root_2849_ = lean_ctor_get(v_t_2848_, 0);
v_tail_2850_ = lean_ctor_get(v_t_2848_, 1);
v___x_2851_ = lean_array_get_size(v_tail_2850_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2846_, v_givenName_2847_, v_tail_2850_, v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2846_, v_givenName_2847_, v_root_2849_);
return v___x_2853_;
}
else
{
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10___boxed(lean_object* v_localDecl_x3f_2854_, lean_object* v_givenName_2855_, lean_object* v_t_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2854_, v_givenName_2855_, v_t_2856_);
lean_dec_ref(v_t_2856_);
lean_dec(v_givenName_2855_);
lean_dec(v_localDecl_x3f_2854_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(lean_object* v_auxDeclToFullName_2858_, lean_object* v_currNamespace_2859_, lean_object* v_decls_2860_, lean_object* v_givenNameView_2861_, uint8_t v_skipAuxDecl_2862_){
_start:
{
lean_object* v_givenName_2863_; lean_object* v_localDecl_x3f_2864_; 
lean_inc_ref(v_givenNameView_2861_);
v_givenName_2863_ = l_Lean_MacroScopesView_review(v_givenNameView_2861_);
v_localDecl_x3f_2864_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2863_, v_skipAuxDecl_2862_, v_auxDeclToFullName_2858_, v_currNamespace_2859_, v_givenNameView_2861_, v_decls_2860_);
if (lean_obj_tag(v_localDecl_x3f_2864_) == 0)
{
if (v_skipAuxDecl_2862_ == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2864_, v_givenName_2863_, v_decls_2860_);
lean_dec(v_givenName_2863_);
return v___x_2865_;
}
else
{
lean_dec(v_givenName_2863_);
return v_localDecl_x3f_2864_;
}
}
else
{
lean_dec(v_givenName_2863_);
return v_localDecl_x3f_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_2866_, lean_object* v_currNamespace_2867_, lean_object* v_decls_2868_, lean_object* v_givenNameView_2869_, lean_object* v_skipAuxDecl_2870_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2871_; lean_object* v_res_2872_; 
v_skipAuxDecl_boxed_2871_ = lean_unbox(v_skipAuxDecl_2870_);
v_res_2872_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(v_auxDeclToFullName_2866_, v_currNamespace_2867_, v_decls_2868_, v_givenNameView_2869_, v_skipAuxDecl_boxed_2871_);
lean_dec_ref(v_decls_2868_);
lean_dec(v_auxDeclToFullName_2866_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(lean_object* v_n_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_lctx_2879_; lean_object* v_decls_2880_; lean_object* v_auxDeclToFullName_2881_; lean_object* v_currNamespace_2882_; lean_object* v_view_2883_; lean_object* v_name_2884_; lean_object* v_findLocalDecl_x3f_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; 
v_lctx_2879_ = lean_ctor_get(v___y_2874_, 2);
v_decls_2880_ = lean_ctor_get(v_lctx_2879_, 1);
v_auxDeclToFullName_2881_ = lean_ctor_get(v_lctx_2879_, 2);
v_currNamespace_2882_ = lean_ctor_get(v___y_2876_, 6);
v_view_2883_ = l_Lean_extractMacroScopes(v_n_2873_);
v_name_2884_ = lean_ctor_get(v_view_2883_, 0);
lean_inc(v_name_2884_);
lean_inc_ref(v_decls_2880_);
lean_inc(v_currNamespace_2882_);
lean_inc(v_auxDeclToFullName_2881_);
v_findLocalDecl_x3f_2885_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_2885_, 0, v_auxDeclToFullName_2881_);
lean_closure_set(v_findLocalDecl_x3f_2885_, 1, v_currNamespace_2882_);
lean_closure_set(v_findLocalDecl_x3f_2885_, 2, v_decls_2880_);
v___x_2886_ = lean_box(0);
v___x_2887_ = 0;
v___x_2888_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2883_, v_findLocalDecl_x3f_2885_, v_name_2884_, v___x_2886_, v___x_2887_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec_ref(v_view_2883_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___boxed(lean_object* v_n_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(uint8_t v___x_2896_, lean_object* v_n_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2917_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2917_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2917_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
if (lean_obj_tag(v_a_2904_) == 0)
{
uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = 1;
v___x_2909_ = lean_box(v___x_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
else
{
lean_object* v___x_2913_; lean_object* v___x_2915_; 
lean_dec_ref_known(v_a_2904_, 1);
v___x_2913_ = lean_box(v___x_2896_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2913_);
v___x_2915_ = v___x_2906_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2918_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2903_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2903_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0___boxed(lean_object* v___x_2926_, lean_object* v_n_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
uint8_t v___x_27798__boxed_2933_; lean_object* v_res_2934_; 
v___x_27798__boxed_2933_ = lean_unbox(v___x_2926_);
v_res_2934_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(v___x_27798__boxed_2933_, v_n_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(lean_object* v_n_u2080_2938_, uint8_t v_fullNames_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v___x_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; 
v___x_2945_ = 0;
v___f_2946_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0));
v___x_2947_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2938_, v_fullNames_2939_, v___x_2945_, v___f_2946_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___boxed(lean_object* v_n_u2080_2948_, lean_object* v_fullNames_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_fullNames_boxed_2955_; lean_object* v_res_2956_; 
v_fullNames_boxed_2955_ = lean_unbox(v_fullNames_2949_);
v_res_2956_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_n_u2080_2948_, v_fullNames_boxed_2955_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2956_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = 1;
return v___x_2959_;
}
else
{
uint8_t v___x_2960_; 
v___x_2960_ = 0;
return v___x_2960_;
}
}
else
{
if (lean_obj_tag(v_x_2958_) == 0)
{
uint8_t v___x_2961_; 
v___x_2961_ = 0;
return v___x_2961_;
}
else
{
lean_object* v_head_2962_; lean_object* v_tail_2963_; lean_object* v_head_2964_; lean_object* v_tail_2965_; uint8_t v___x_2966_; 
v_head_2962_ = lean_ctor_get(v_x_2957_, 0);
v_tail_2963_ = lean_ctor_get(v_x_2957_, 1);
v_head_2964_ = lean_ctor_get(v_x_2958_, 0);
v_tail_2965_ = lean_ctor_get(v_x_2958_, 1);
v___x_2966_ = lean_string_dec_eq(v_head_2962_, v_head_2964_);
if (v___x_2966_ == 0)
{
return v___x_2966_;
}
else
{
v_x_2957_ = v_tail_2963_;
v_x_2958_ = v_tail_2965_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3___boxed(lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
uint8_t v_res_2970_; lean_object* v_r_2971_; 
v_res_2970_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_x_2968_, v_x_2969_);
lean_dec(v_x_2969_);
lean_dec(v_x_2968_);
v_r_2971_ = lean_box(v_res_2970_);
return v_r_2971_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(lean_object* v_x_2972_, lean_object* v_x_2973_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
if (lean_obj_tag(v_x_2973_) == 0)
{
uint8_t v___x_2974_; 
v___x_2974_ = 1;
return v___x_2974_;
}
else
{
uint8_t v___x_2975_; 
v___x_2975_ = 0;
return v___x_2975_;
}
}
else
{
if (lean_obj_tag(v_x_2973_) == 0)
{
uint8_t v___x_2976_; 
v___x_2976_ = 0;
return v___x_2976_;
}
else
{
lean_object* v_head_2977_; lean_object* v_tail_2978_; lean_object* v_head_2979_; lean_object* v_tail_2980_; uint8_t v___y_2982_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v_fst_2986_; lean_object* v_snd_2987_; uint8_t v___x_2988_; 
v_head_2977_ = lean_ctor_get(v_x_2972_, 0);
v_tail_2978_ = lean_ctor_get(v_x_2972_, 1);
v_head_2979_ = lean_ctor_get(v_x_2973_, 0);
v_tail_2980_ = lean_ctor_get(v_x_2973_, 1);
v_fst_2984_ = lean_ctor_get(v_head_2977_, 0);
v_snd_2985_ = lean_ctor_get(v_head_2977_, 1);
v_fst_2986_ = lean_ctor_get(v_head_2979_, 0);
v_snd_2987_ = lean_ctor_get(v_head_2979_, 1);
v___x_2988_ = lean_name_eq(v_fst_2984_, v_fst_2986_);
if (v___x_2988_ == 0)
{
v___y_2982_ = v___x_2988_;
goto v___jp_2981_;
}
else
{
uint8_t v___x_2989_; 
v___x_2989_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_snd_2985_, v_snd_2987_);
v___y_2982_ = v___x_2989_;
goto v___jp_2981_;
}
v___jp_2981_:
{
if (v___y_2982_ == 0)
{
return v___y_2982_;
}
else
{
v_x_2972_ = v_tail_2978_;
v_x_2973_ = v_tail_2980_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1___boxed(lean_object* v_x_2990_, lean_object* v_x_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_x_2990_, v_x_2991_);
lean_dec(v_x_2991_);
lean_dec(v_x_2990_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_2996_ = l_Lean_stringToMessageData(v___x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_2997_, lean_object* v_newName_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_ref_3004_; 
v_ref_3004_ = lean_ctor_get(v_a_3001_, 5);
if (lean_obj_tag(v_ref_3004_) == 3)
{
lean_object* v_val_3005_; uint8_t v___x_3006_; 
v_val_3005_ = lean_ctor_get(v_ref_3004_, 2);
v___x_3006_ = l_Lean_Name_hasMacroScopes(v_val_3005_);
if (v___x_3006_ == 0)
{
uint8_t v___x_3007_; lean_object* v___x_3085_; 
v___x_3007_ = 1;
v___x_3085_ = l_Lean_Syntax_getRange_x3f(v_ref_3004_, v___x_3007_);
if (lean_obj_tag(v___x_3085_) == 0)
{
if (v___x_3006_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v_newName_2998_);
lean_dec(v_declName_2997_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
else
{
goto v___jp_3008_;
}
}
else
{
lean_dec_ref_known(v___x_3085_, 1);
goto v___jp_3008_;
}
v___jp_3008_:
{
lean_object* v___x_3009_; 
lean_inc(v_val_3005_);
v___x_3009_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_val_3005_, v___x_3007_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3076_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3076_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3076_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v_declName_2997_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___x_3014_);
v___x_3017_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_a_3010_, v___x_3016_);
lean_dec_ref_known(v___x_3016_, 2);
lean_dec(v_a_3010_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
lean_dec(v_newName_2998_);
v___x_3018_ = lean_box(0);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3018_);
v___x_3020_ = v___x_3012_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
else
{
lean_object* v___x_3022_; 
lean_del_object(v___x_3012_);
v___x_3022_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_newName_2998_, v___x_3006_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3067_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3067_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3067_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
if (lean_obj_tag(v_a_3023_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3025_);
v_val_3027_ = lean_ctor_get(v_a_3023_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_a_3023_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3029_ = v_a_3023_;
v_isShared_3030_ = v_isSharedCheck_3062_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_val_3027_);
lean_dec(v_a_3023_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3062_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3031_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3032_ = l_Lean_Name_toString(v_val_3027_, v___x_3007_);
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
lean_ctor_set(v___x_3035_, 3, v___x_3034_);
lean_ctor_set(v___x_3035_, 4, v___x_3034_);
lean_ctor_set(v___x_3035_, 5, v___x_3034_);
v___x_3036_ = 0;
v___x_3037_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3034_);
lean_ctor_set(v___x_3037_, 2, v___x_3034_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*3, v___x_3036_);
v___x_3038_ = lean_unsigned_to_nat(1u);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_3038_);
v___x_3040_ = lean_array_push(v___x_3039_, v___x_3037_);
lean_inc_ref(v_ref_3004_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v_ref_3004_);
v___x_3042_ = v___x_3029_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_ref_3004_);
v___x_3042_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_MessageData_hint(v___x_3031_, v___x_3040_, v___x_3042_, v___x_3034_, v___x_3006_, v_a_3001_, v_a_3002_);
lean_dec_ref(v___x_3040_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3052_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3043_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3043_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
lean_dec(v_a_3023_);
v___x_3063_ = lean_box(0);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3063_);
v___x_3065_ = v___x_3025_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_a_3068_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3022_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3022_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_newName_2998_);
lean_dec(v_declName_2997_);
v_a_3077_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3009_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3009_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_newName_2998_);
lean_dec(v_declName_2997_);
v___x_3088_ = lean_box(0);
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
return v___x_3089_;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v_newName_2998_);
lean_dec(v_declName_2997_);
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3092_, lean_object* v_newName_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3092_, v_newName_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(lean_object* v_opt_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_3100_, v___y_3103_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_opt_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(v_opt_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_opt_3107_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(lean_object* v_00_u03b4_3114_, lean_object* v_t_3115_, lean_object* v_k_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_3115_, v_k_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b4_3118_, lean_object* v_t_3119_, lean_object* v_k_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(v_00_u03b4_3118_, v_t_3119_, v_k_3120_);
lean_dec(v_k_3120_);
lean_dec(v_t_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(lean_object* v_givenName_3122_, uint8_t v_skipAuxDecl_3123_, lean_object* v_auxDeclToFullName_3124_, lean_object* v___x_3125_, lean_object* v_givenNameView_3126_, lean_object* v_as_3127_, lean_object* v_i_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_3122_, v_skipAuxDecl_3123_, v_auxDeclToFullName_3124_, v___x_3125_, v_givenNameView_3126_, v_as_3127_, v_i_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_givenName_3131_, lean_object* v_skipAuxDecl_3132_, lean_object* v_auxDeclToFullName_3133_, lean_object* v___x_3134_, lean_object* v_givenNameView_3135_, lean_object* v_as_3136_, lean_object* v_i_3137_, lean_object* v_a_3138_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3139_; lean_object* v_res_3140_; 
v_skipAuxDecl_boxed_3139_ = lean_unbox(v_skipAuxDecl_3132_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(v_givenName_3131_, v_skipAuxDecl_boxed_3139_, v_auxDeclToFullName_3133_, v___x_3134_, v_givenNameView_3135_, v_as_3136_, v_i_3137_, v_a_3138_);
lean_dec_ref(v_as_3136_);
lean_dec(v_auxDeclToFullName_3133_);
lean_dec(v_givenName_3131_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(lean_object* v_localDecl_x3f_3141_, lean_object* v_givenName_3142_, lean_object* v_as_3143_, lean_object* v_i_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_3141_, v_givenName_3142_, v_as_3143_, v_i_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___boxed(lean_object* v_localDecl_x3f_3147_, lean_object* v_givenName_3148_, lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(v_localDecl_x3f_3147_, v_givenName_3148_, v_as_3149_, v_i_3150_, v_a_3151_);
lean_dec_ref(v_as_3149_);
lean_dec(v_givenName_3148_);
lean_dec(v_localDecl_x3f_3147_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(lean_object* v_n_u2080_3153_, lean_object* v_filter_3154_, lean_object* v_view_x3f_3155_, lean_object* v_as_3156_, lean_object* v_as_x27_3157_, lean_object* v_b_3158_, lean_object* v_a_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_3153_, v_filter_3154_, v_view_x3f_3155_, v_as_x27_3157_, v_b_3158_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_n_u2080_3166_, lean_object* v_filter_3167_, lean_object* v_view_x3f_3168_, lean_object* v_as_3169_, lean_object* v_as_x27_3170_, lean_object* v_b_3171_, lean_object* v_a_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(v_n_u2080_3166_, v_filter_3167_, v_view_x3f_3168_, v_as_3169_, v_as_x27_3170_, v_b_3171_, v_a_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v_as_x27_3170_);
lean_dec(v_as_3169_);
lean_dec(v_n_u2080_3166_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(lean_object* v_givenName_3179_, uint8_t v_skipAuxDecl_3180_, lean_object* v_auxDeclToFullName_3181_, lean_object* v___x_3182_, lean_object* v_givenNameView_3183_, lean_object* v_as_3184_, lean_object* v_i_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_3179_, v_skipAuxDecl_3180_, v_auxDeclToFullName_3181_, v___x_3182_, v_givenNameView_3183_, v_as_3184_, v_i_3185_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___boxed(lean_object* v_givenName_3188_, lean_object* v_skipAuxDecl_3189_, lean_object* v_auxDeclToFullName_3190_, lean_object* v___x_3191_, lean_object* v_givenNameView_3192_, lean_object* v_as_3193_, lean_object* v_i_3194_, lean_object* v_a_3195_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3196_; lean_object* v_res_3197_; 
v_skipAuxDecl_boxed_3196_ = lean_unbox(v_skipAuxDecl_3189_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(v_givenName_3188_, v_skipAuxDecl_boxed_3196_, v_auxDeclToFullName_3190_, v___x_3191_, v_givenNameView_3192_, v_as_3193_, v_i_3194_, v_a_3195_);
lean_dec_ref(v_as_3193_);
lean_dec(v_auxDeclToFullName_3190_);
lean_dec(v_givenName_3188_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(lean_object* v_localDecl_x3f_3198_, lean_object* v_givenName_3199_, lean_object* v_as_3200_, lean_object* v_i_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_3198_, v_givenName_3199_, v_as_3200_, v_i_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___boxed(lean_object* v_localDecl_x3f_3204_, lean_object* v_givenName_3205_, lean_object* v_as_3206_, lean_object* v_i_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(v_localDecl_x3f_3204_, v_givenName_3205_, v_as_3206_, v_i_3207_, v_a_3208_);
lean_dec_ref(v_as_3206_);
lean_dec(v_givenName_3205_);
lean_dec(v_localDecl_x3f_3204_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(lean_object* v_opt_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_3210_, v___y_3213_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___boxed(lean_object* v_opt_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(v_opt_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v_opt_3217_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; lean_object* v_env_3228_; lean_object* v___x_3229_; lean_object* v_toEnvExtension_3230_; lean_object* v_asyncMode_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_merged_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3243_; 
v___x_3227_ = lean_st_ref_get(v___y_3225_);
v_env_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3227_);
v___x_3229_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3230_ = lean_ctor_get(v___x_3229_, 0);
v_asyncMode_3231_ = lean_ctor_get(v_toEnvExtension_3230_, 2);
v___x_3232_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3233_ = lean_box(0);
v___x_3234_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3232_, v___x_3229_, v_env_3228_, v_asyncMode_3231_, v___x_3233_);
v_merged_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3234_, 1);
lean_dec(v_unused_3244_);
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_merged_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 1, v_merged_3235_);
lean_ctor_set(v___x_3237_, 0, v_o_3224_);
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_o_3224_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_merged_3235_);
v___x_3240_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3245_, v___y_3246_);
lean_dec(v___y_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_options_3254_; lean_object* v___x_3255_; 
v_options_3254_ = lean_ctor_get(v___y_3251_, 2);
lean_inc_ref(v_options_3254_);
v___x_3255_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_3254_, v___y_3252_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
return v_res_3261_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3264_ = l_Lean_stringToMessageData(v___x_3263_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3267_ = l_Lean_stringToMessageData(v___x_3266_);
return v___x_3267_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3270_ = l_Lean_stringToMessageData(v___x_3269_);
return v___x_3270_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3273_ = l_Lean_stringToMessageData(v___x_3272_);
return v___x_3273_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3276_ = l_Lean_stringToMessageData(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3279_ = l_Lean_stringToMessageData(v___x_3278_);
return v___x_3279_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3282_ = l_Lean_stringToMessageData(v___x_3281_);
return v___x_3282_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3286_ = l_Lean_MessageData_ofFormat(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3298_ = l_Lean_stringToMessageData(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3304_ = l_Lean_stringToMessageData(v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3305_, uint8_t v_allowSuggestion_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3485_; 
v___x_3312_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3485_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3485_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v_extraMsg_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; 
v___x_3317_ = l_Lean_Linter_linter_deprecated;
v___x_3318_ = l_Lean_Linter_getLinterValue(v___x_3317_, v_a_3313_);
lean_dec(v_a_3313_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_dec(v_declName_3305_);
v___x_3334_ = lean_box(0);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3334_);
v___x_3336_ = v___x_3315_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
else
{
lean_object* v___x_3338_; lean_object* v_env_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3338_ = lean_st_ref_get(v_a_3310_);
v_env_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_env_3339_);
lean_dec(v___x_3338_);
v___x_3340_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3341_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3305_);
v___x_3342_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3340_, v___x_3341_, v_env_3339_, v_declName_3305_);
if (lean_obj_tag(v___x_3342_) == 1)
{
lean_object* v_val_3343_; lean_object* v_text_x3f_3344_; 
lean_del_object(v___x_3315_);
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v_text_x3f_3344_ = lean_ctor_get(v_val_3343_, 1);
if (lean_obj_tag(v_text_x3f_3344_) == 0)
{
lean_object* v_newName_x3f_3345_; 
v_newName_x3f_3345_ = lean_ctor_get(v_val_3343_, 0);
lean_inc(v_newName_x3f_3345_);
lean_dec(v_val_3343_);
if (lean_obj_tag(v_newName_x3f_3345_) == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_3320_ = v___x_3346_;
v___y_3321_ = v_a_3307_;
v___y_3322_ = v_a_3308_;
v___y_3323_ = v_a_3309_;
v___y_3324_ = v_a_3310_;
goto v___jp_3319_;
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3348_; lean_object* v_env_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; 
v_val_3347_ = lean_ctor_get(v_newName_x3f_3345_, 0);
lean_inc_n(v_val_3347_, 2);
lean_dec_ref_known(v_newName_x3f_3345_, 1);
v___x_3348_ = lean_st_ref_get(v_a_3310_);
v_env_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_ref_n(v_env_3349_, 2);
lean_dec(v___x_3348_);
v___x_3350_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3351_ = l_Lean_MessageData_ofConstName(v_val_3347_, v___x_3318_);
lean_inc_ref(v___x_3351_);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_Name_getPrefix(v_declName_3305_);
v___x_3356_ = 0;
lean_inc(v_declName_3305_);
v___x_3357_ = l_Lean_Environment_find_x3f(v_env_3349_, v_declName_3305_, v___x_3356_);
if (lean_obj_tag(v___x_3357_) == 1)
{
lean_object* v_val_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_val_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = l_Lean_Name_getPrefix(v_val_3347_);
lean_inc(v_val_3347_);
lean_inc_ref(v_env_3349_);
v___x_3360_ = l_Lean_Environment_find_x3f(v_env_3349_, v_val_3347_, v___x_3356_);
if (lean_obj_tag(v___x_3360_) == 1)
{
lean_object* v_val_3361_; lean_object* v___x_3362_; 
v_val_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3358_, v_val_3361_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v_msg_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v_msg_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; uint8_t v___x_3457_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3457_ = lean_unbox(v_a_3363_);
if (v___x_3457_ == 0)
{
if (v___x_3318_ == 0)
{
lean_dec(v_val_3361_);
lean_dec(v_val_3358_);
v_msg_3450_ = v___x_3354_;
v___y_3451_ = v_a_3307_;
v___y_3452_ = v_a_3308_;
v___y_3453_ = v_a_3309_;
v___y_3454_ = v_a_3310_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3458_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_3459_ = l_Lean_ConstantInfo_type(v_val_3361_);
lean_dec(v_val_3361_);
v___x_3460_ = l_Lean_indentExpr(v___x_3459_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3458_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_ConstantInfo_type(v_val_3358_);
lean_dec(v_val_3358_);
v___x_3465_ = l_Lean_indentExpr(v___x_3464_);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3463_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_MessageData_note(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3354_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v_msg_3450_ = v___x_3468_;
v___y_3451_ = v_a_3307_;
v___y_3452_ = v_a_3308_;
v___y_3453_ = v_a_3309_;
v___y_3454_ = v_a_3310_;
goto v___jp_3449_;
}
}
else
{
lean_dec(v_val_3361_);
lean_dec(v_val_3358_);
v_msg_3450_ = v___x_3354_;
v___y_3451_ = v_a_3307_;
v___y_3452_ = v_a_3308_;
v___y_3453_ = v_a_3309_;
v___y_3454_ = v_a_3310_;
goto v___jp_3449_;
}
v___jp_3364_:
{
if (v_allowSuggestion_3306_ == 0)
{
lean_dec(v_a_3363_);
lean_dec(v_val_3347_);
v_extraMsg_3320_ = v_msg_3365_;
v___y_3321_ = v___y_3366_;
v___y_3322_ = v___y_3367_;
v___y_3323_ = v___y_3368_;
v___y_3324_ = v___y_3369_;
goto v___jp_3319_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_unbox(v_a_3363_);
lean_dec(v_a_3363_);
if (v___x_3370_ == 0)
{
lean_dec(v_val_3347_);
v_extraMsg_3320_ = v_msg_3365_;
v___y_3321_ = v___y_3366_;
v___y_3322_ = v___y_3367_;
v___y_3323_ = v___y_3368_;
v___y_3324_ = v___y_3369_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3371_; 
lean_inc(v_declName_3305_);
v___x_3371_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3305_, v_val_3347_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
if (lean_obj_tag(v_a_3372_) == 1)
{
lean_object* v_val_3373_; lean_object* v___x_3374_; 
v_val_3373_ = lean_ctor_get(v_a_3372_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v_a_3372_, 1);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_msg_3365_);
lean_ctor_set(v___x_3374_, 1, v_val_3373_);
v_extraMsg_3320_ = v___x_3374_;
v___y_3321_ = v___y_3366_;
v___y_3322_ = v___y_3367_;
v___y_3323_ = v___y_3368_;
v___y_3324_ = v___y_3369_;
goto v___jp_3319_;
}
else
{
lean_dec(v_a_3372_);
v_extraMsg_3320_ = v_msg_3365_;
v___y_3321_ = v___y_3366_;
v___y_3322_ = v___y_3367_;
v___y_3323_ = v___y_3368_;
v___y_3324_ = v___y_3369_;
goto v___jp_3319_;
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v_msg_3365_);
lean_dec(v_declName_3305_);
v_a_3375_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3371_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3371_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
v___jp_3383_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3390_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3351_);
v___x_3392_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___y_3389_);
v___x_3395_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_MessageData_ofName(v___x_3359_);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_MessageData_note(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___y_3387_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v_msg_3365_ = v___x_3402_;
v___y_3366_ = v___y_3386_;
v___y_3367_ = v___y_3385_;
v___y_3368_ = v___y_3384_;
v___y_3369_ = v___y_3388_;
goto v___jp_3364_;
}
v___jp_3403_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3410_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___y_3409_);
v___x_3412_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = l_Lean_MessageData_note(v___x_3413_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3407_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v_msg_3365_ = v___x_3415_;
v___y_3366_ = v___y_3406_;
v___y_3367_ = v___y_3405_;
v___y_3368_ = v___y_3404_;
v___y_3369_ = v___y_3408_;
goto v___jp_3364_;
}
v___jp_3416_:
{
if (v___y_3423_ == 0)
{
uint8_t v___x_3424_; 
lean_inc(v_declName_3305_);
lean_inc_ref(v_env_3349_);
v___x_3424_ = l_Lean_isProtected(v_env_3349_, v_declName_3305_);
if (v___x_3424_ == 0)
{
if (v___x_3318_ == 0)
{
lean_dec(v___x_3359_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
v_msg_3365_ = v___y_3421_;
v___y_3366_ = v___y_3420_;
v___y_3367_ = v___y_3418_;
v___y_3368_ = v___y_3417_;
v___y_3369_ = v___y_3422_;
goto v___jp_3364_;
}
else
{
uint8_t v___x_3425_; 
lean_inc(v_val_3347_);
v___x_3425_ = l_Lean_isProtected(v_env_3349_, v_val_3347_);
if (v___x_3425_ == 0)
{
lean_dec(v___x_3359_);
lean_dec_ref(v___x_3351_);
v_msg_3365_ = v___y_3421_;
v___y_3366_ = v___y_3420_;
v___y_3367_ = v___y_3418_;
v___y_3368_ = v___y_3417_;
v___y_3369_ = v___y_3422_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
lean_inc(v___x_3359_);
v___x_3426_ = l_Lean_Name_componentsRev(v___x_3359_);
v___x_3427_ = lean_unsigned_to_nat(1u);
v___x_3428_ = l_List_lengthTR___redArg(v___x_3426_);
v___x_3429_ = lean_nat_dec_lt(v___x_3427_, v___x_3428_);
lean_dec(v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v___x_3426_);
v___x_3430_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3384_ = v___y_3417_;
v___y_3385_ = v___y_3418_;
v___y_3386_ = v___y_3420_;
v___y_3387_ = v___y_3421_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___x_3430_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3431_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = l_List_get___redArg(v___x_3426_, v___x_3432_);
lean_dec(v___x_3426_);
v___x_3434_ = l_Lean_MessageData_ofName(v___x_3433_);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3431_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___y_3384_ = v___y_3417_;
v___y_3385_ = v___y_3418_;
v___y_3386_ = v___y_3420_;
v___y_3387_ = v___y_3421_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___x_3437_;
goto v___jp_3383_;
}
}
}
}
else
{
lean_dec(v___x_3359_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
v_msg_3365_ = v___y_3421_;
v___y_3366_ = v___y_3420_;
v___y_3367_ = v___y_3418_;
v___y_3368_ = v___y_3417_;
v___y_3369_ = v___y_3422_;
goto v___jp_3364_;
}
}
else
{
lean_dec(v___x_3359_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
if (lean_obj_tag(v_declName_3305_) == 1)
{
lean_object* v_str_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v_str_3438_ = lean_ctor_get(v_declName_3305_, 1);
v___x_3439_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3438_);
v___x_3440_ = l_Lean_stringToMessageData(v_str_3438_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
lean_inc(v_val_3347_);
v___x_3444_ = l_Lean_MessageData_ofConstName(v_val_3347_, v___y_3419_);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___y_3404_ = v___y_3417_;
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v___y_3422_;
v___y_3409_ = v___x_3447_;
goto v___jp_3403_;
}
else
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_MessageData_nil;
v___y_3404_ = v___y_3417_;
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v___y_3422_;
v___y_3409_ = v___x_3448_;
goto v___jp_3403_;
}
}
}
v___jp_3449_:
{
uint8_t v___x_3455_; 
v___x_3455_ = l_Lean_Name_isAnonymous(v___x_3355_);
if (v___x_3455_ == 0)
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_name_eq(v___x_3355_, v___x_3359_);
lean_dec(v___x_3355_);
if (v___x_3456_ == 0)
{
v___y_3417_ = v___y_3453_;
v___y_3418_ = v___y_3452_;
v___y_3419_ = v___x_3455_;
v___y_3420_ = v___y_3451_;
v___y_3421_ = v_msg_3450_;
v___y_3422_ = v___y_3454_;
v___y_3423_ = v___x_3318_;
goto v___jp_3416_;
}
else
{
v___y_3417_ = v___y_3453_;
v___y_3418_ = v___y_3452_;
v___y_3419_ = v___x_3455_;
v___y_3420_ = v___y_3451_;
v___y_3421_ = v_msg_3450_;
v___y_3422_ = v___y_3454_;
v___y_3423_ = v___x_3455_;
goto v___jp_3416_;
}
}
else
{
lean_dec(v___x_3359_);
lean_dec(v___x_3355_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
v_msg_3365_ = v_msg_3450_;
v___y_3366_ = v___y_3451_;
v___y_3367_ = v___y_3452_;
v___y_3368_ = v___y_3453_;
v___y_3369_ = v___y_3454_;
goto v___jp_3364_;
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_val_3361_);
lean_dec(v___x_3359_);
lean_dec(v_val_3358_);
lean_dec(v___x_3355_);
lean_dec_ref_known(v___x_3354_, 2);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
lean_dec(v_val_3347_);
lean_dec(v_declName_3305_);
v_a_3469_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3362_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3362_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_dec(v___x_3360_);
lean_dec(v___x_3359_);
lean_dec(v_val_3358_);
lean_dec(v___x_3355_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
lean_dec(v_val_3347_);
v_extraMsg_3320_ = v___x_3354_;
v___y_3321_ = v_a_3307_;
v___y_3322_ = v_a_3308_;
v___y_3323_ = v_a_3309_;
v___y_3324_ = v_a_3310_;
goto v___jp_3319_;
}
}
else
{
lean_dec(v___x_3357_);
lean_dec(v___x_3355_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_env_3349_);
lean_dec(v_val_3347_);
v_extraMsg_3320_ = v___x_3354_;
v___y_3321_ = v_a_3307_;
v___y_3322_ = v_a_3308_;
v___y_3323_ = v_a_3309_;
v___y_3324_ = v_a_3310_;
goto v___jp_3319_;
}
}
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_inc_ref(v_text_x3f_3344_);
lean_dec(v_val_3343_);
v_val_3477_ = lean_ctor_get(v_text_x3f_3344_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_text_x3f_3344_, 1);
v___x_3478_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3479_ = l_Lean_stringToMessageData(v_val_3477_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v_extraMsg_3320_ = v___x_3480_;
v___y_3321_ = v_a_3307_;
v___y_3322_ = v_a_3308_;
v___y_3323_ = v_a_3309_;
v___y_3324_ = v_a_3310_;
goto v___jp_3319_;
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
lean_dec(v___x_3342_);
lean_dec(v_declName_3305_);
v___x_3481_ = lean_box(0);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3481_);
v___x_3483_ = v___x_3315_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
v___jp_3319_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_));
v___x_3326_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_);
v___x_3327_ = l_Lean_MessageData_ofConstName(v_declName_3305_, v___x_3318_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v_extraMsg_3320_);
v___x_3332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3325_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_3332_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3486_, lean_object* v_allowSuggestion_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
uint8_t v_allowSuggestion_boxed_3493_; lean_object* v_res_3494_; 
v_allowSuggestion_boxed_3493_ = lean_unbox(v_allowSuggestion_3487_);
v_res_3494_ = l_Lean_Linter_checkDeprecated(v_declName_3486_, v_allowSuggestion_boxed_3493_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3495_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3508_;
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
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1402858700____hygCtx___hyg_2_();
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
