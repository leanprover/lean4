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
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(lean_object* v_opts_145_, lean_object* v_opt_146_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4___boxed(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_opts_155_, v_opt_156_);
lean_dec_ref(v_opt_156_);
lean_dec_ref(v_opts_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(lean_object* v_x_159_, lean_object* v_x_160_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(uint8_t v___x_171_, lean_object* v_env_172_, lean_object* v_n_173_, lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lean_Environment_contains(v_env_172_, v_n_173_, v___x_171_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_176_, lean_object* v_env_177_, lean_object* v_n_178_, lean_object* v_x_179_){
_start:
{
uint8_t v___x_42750__boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v___x_42750__boxed_180_ = lean_unbox(v___x_176_);
v_res_181_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_42750__boxed_180_, v_env_177_, v_n_178_, v_x_179_);
lean_dec_ref(v_x_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_186_);
lean_dec_ref(v_x_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v_x_195_, v_x_196_, v_x_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v_x_197_);
lean_dec_ref(v_x_196_);
lean_dec(v_x_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l_List_reverse___redArg(v_a_202_);
return v___x_203_;
}
else
{
lean_object* v_head_204_; lean_object* v_tail_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_216_; 
v_head_204_ = lean_ctor_get(v_a_201_, 0);
v_tail_205_ = lean_ctor_get(v_a_201_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_216_ == 0)
{
v___x_207_ = v_a_201_;
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_tail_205_);
lean_inc(v_head_204_);
lean_dec(v_a_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_216_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_snd_209_; uint8_t v___x_210_; 
v_snd_209_ = lean_ctor_get(v_head_204_, 1);
v___x_210_ = l_List_isEmpty___redArg(v_snd_209_);
if (v___x_210_ == 0)
{
lean_del_object(v___x_207_);
lean_dec(v_head_204_);
v_a_201_ = v_tail_205_;
goto _start;
}
else
{
lean_object* v___x_213_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_a_202_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_head_204_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_a_202_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_a_201_ = v_tail_205_;
v_a_202_ = v___x_213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(lean_object* v_msgData_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_env_224_; lean_object* v___x_225_; lean_object* v_mctx_226_; lean_object* v_lctx_227_; lean_object* v_options_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_env_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_env_224_);
lean_dec(v___x_223_);
v___x_225_ = lean_st_ref_get(v___y_219_);
v_mctx_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_mctx_226_);
lean_dec(v___x_225_);
v_lctx_227_ = lean_ctor_get(v___y_218_, 2);
v_options_228_ = lean_ctor_get(v___y_220_, 2);
lean_inc_ref(v_options_228_);
lean_inc_ref(v_lctx_227_);
v___x_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_229_, 0, v_env_224_);
lean_ctor_set(v___x_229_, 1, v_mctx_226_);
lean_ctor_set(v___x_229_, 2, v_lctx_227_);
lean_ctor_set(v___x_229_, 3, v_options_228_);
v___x_230_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_msgData_217_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47___boxed(lean_object* v_msgData_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v_msgData_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(uint8_t v_suppressElabErrors_247_, uint8_t v___y_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 1)
{
lean_object* v_pre_250_; 
v_pre_250_ = lean_ctor_get(v_x_249_, 0);
switch(lean_obj_tag(v_pre_250_))
{
case 1:
{
lean_object* v_pre_251_; 
v_pre_251_ = lean_ctor_get(v_pre_250_, 0);
switch(lean_obj_tag(v_pre_251_))
{
case 0:
{
lean_object* v_str_252_; lean_object* v_str_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_str_252_ = lean_ctor_get(v_x_249_, 1);
v_str_253_ = lean_ctor_get(v_pre_250_, 1);
v___x_254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__0));
v___x_255_ = lean_string_dec_eq(v_str_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__1));
v___x_257_ = lean_string_dec_eq(v_str_253_, v___x_256_);
if (v___x_257_ == 0)
{
return v___x_257_;
}
else
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__2));
v___x_259_ = lean_string_dec_eq(v_str_252_, v___x_258_);
if (v___x_259_ == 0)
{
return v___x_259_;
}
else
{
return v_suppressElabErrors_247_;
}
}
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__3));
v___x_261_ = lean_string_dec_eq(v_str_252_, v___x_260_);
if (v___x_261_ == 0)
{
return v___x_261_;
}
else
{
return v_suppressElabErrors_247_;
}
}
}
case 1:
{
lean_object* v_pre_262_; 
v_pre_262_ = lean_ctor_get(v_pre_251_, 0);
if (lean_obj_tag(v_pre_262_) == 0)
{
lean_object* v_str_263_; lean_object* v_str_264_; lean_object* v_str_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_str_263_ = lean_ctor_get(v_x_249_, 1);
v_str_264_ = lean_ctor_get(v_pre_250_, 1);
v_str_265_ = lean_ctor_get(v_pre_251_, 1);
v___x_266_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__4));
v___x_267_ = lean_string_dec_eq(v_str_265_, v___x_266_);
if (v___x_267_ == 0)
{
return v___x_267_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__5));
v___x_269_ = lean_string_dec_eq(v_str_264_, v___x_268_);
if (v___x_269_ == 0)
{
return v___x_269_;
}
else
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__6));
v___x_271_ = lean_string_dec_eq(v_str_263_, v___x_270_);
if (v___x_271_ == 0)
{
return v___x_271_;
}
else
{
return v_suppressElabErrors_247_;
}
}
}
}
else
{
return v___y_248_;
}
}
default: 
{
return v___y_248_;
}
}
}
case 0:
{
lean_object* v_str_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_str_272_ = lean_ctor_get(v_x_249_, 1);
v___x_273_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___closed__7));
v___x_274_ = lean_string_dec_eq(v_str_272_, v___x_273_);
if (v___x_274_ == 0)
{
return v___x_274_;
}
else
{
return v_suppressElabErrors_247_;
}
}
default: 
{
return v___y_248_;
}
}
}
else
{
return v___y_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_275_, lean_object* v___y_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_suppressElabErrors_boxed_278_; uint8_t v___y_42859__boxed_279_; uint8_t v_res_280_; lean_object* v_r_281_; 
v_suppressElabErrors_boxed_278_ = lean_unbox(v_suppressElabErrors_275_);
v___y_42859__boxed_279_ = lean_unbox(v___y_276_);
v_res_280_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0(v_suppressElabErrors_boxed_278_, v___y_42859__boxed_279_, v_x_277_);
lean_dec(v_x_277_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(lean_object* v_ref_283_, lean_object* v_msgData_284_, uint8_t v_severity_285_, uint8_t v_isSilent_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___y_293_; uint8_t v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; uint8_t v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; uint8_t v___y_335_; lean_object* v___y_336_; lean_object* v___y_354_; lean_object* v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; uint8_t v___y_370_; uint8_t v___y_371_; uint8_t v___x_376_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; uint8_t v___y_382_; uint8_t v___y_383_; uint8_t v___y_384_; uint8_t v___y_386_; uint8_t v___x_401_; 
v___x_376_ = 2;
v___x_401_ = l_Lean_instBEqMessageSeverity_beq(v_severity_285_, v___x_376_);
if (v___x_401_ == 0)
{
v___y_386_ = v___x_401_;
goto v___jp_385_;
}
else
{
uint8_t v___x_402_; 
lean_inc_ref(v_msgData_284_);
v___x_402_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_284_);
v___y_386_ = v___x_402_;
goto v___jp_385_;
}
v___jp_292_:
{
lean_object* v___x_302_; lean_object* v_currNamespace_303_; lean_object* v_openDecls_304_; lean_object* v_env_305_; lean_object* v_nextMacroScope_306_; lean_object* v_ngen_307_; lean_object* v_auxDeclNGen_308_; lean_object* v_traceState_309_; lean_object* v_cache_310_; lean_object* v_messages_311_; lean_object* v_infoState_312_; lean_object* v_snapshotTasks_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_327_; 
v___x_302_ = lean_st_ref_take(v___y_301_);
v_currNamespace_303_ = lean_ctor_get(v___y_300_, 6);
v_openDecls_304_ = lean_ctor_get(v___y_300_, 7);
v_env_305_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_306_ = lean_ctor_get(v___x_302_, 1);
v_ngen_307_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_308_ = lean_ctor_get(v___x_302_, 3);
v_traceState_309_ = lean_ctor_get(v___x_302_, 4);
v_cache_310_ = lean_ctor_get(v___x_302_, 5);
v_messages_311_ = lean_ctor_get(v___x_302_, 6);
v_infoState_312_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_313_ = lean_ctor_get(v___x_302_, 8);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_327_ == 0)
{
v___x_315_ = v___x_302_;
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snapshotTasks_313_);
lean_inc(v_infoState_312_);
lean_inc(v_messages_311_);
lean_inc(v_cache_310_);
lean_inc(v_traceState_309_);
lean_inc(v_auxDeclNGen_308_);
lean_inc(v_ngen_307_);
lean_inc(v_nextMacroScope_306_);
lean_inc(v_env_305_);
lean_dec(v___x_302_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
lean_inc(v_openDecls_304_);
lean_inc(v_currNamespace_303_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_currNamespace_303_);
lean_ctor_set(v___x_317_, 1, v_openDecls_304_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___y_297_);
lean_inc_ref(v___y_293_);
lean_inc_ref(v___y_295_);
v___x_319_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_319_, 0, v___y_295_);
lean_ctor_set(v___x_319_, 1, v___y_299_);
lean_ctor_set(v___x_319_, 2, v___y_298_);
lean_ctor_set(v___x_319_, 3, v___y_293_);
lean_ctor_set(v___x_319_, 4, v___x_318_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5, v___y_296_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5 + 1, v___y_294_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5 + 2, v_isSilent_286_);
v___x_320_ = l_Lean_MessageLog_add(v___x_319_, v_messages_311_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 6, v___x_320_);
v___x_322_ = v___x_315_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_env_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_traceState_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_cache_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_infoState_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_snapshotTasks_313_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_st_ref_put(v___y_301_, v___x_322_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
}
v___jp_328_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_352_; 
v___x_337_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_284_);
v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_337_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_352_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_inc_ref_n(v___y_330_, 2);
v___x_343_ = l_Lean_FileMap_toPosition(v___y_330_, v___y_334_);
lean_dec(v___y_334_);
v___x_344_ = l_Lean_FileMap_toPosition(v___y_330_, v___y_336_);
lean_dec(v___y_336_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_332_ == 0)
{
lean_del_object(v___x_341_);
lean_dec_ref(v___y_329_);
v___y_293_ = v___x_346_;
v___y_294_ = v___y_331_;
v___y_295_ = v___y_333_;
v___y_296_ = v___y_335_;
v___y_297_ = v_a_339_;
v___y_298_ = v___x_345_;
v___y_299_ = v___x_343_;
v___y_300_ = v___y_289_;
v___y_301_ = v___y_290_;
goto v___jp_292_;
}
else
{
uint8_t v___x_347_; 
lean_inc(v_a_339_);
v___x_347_ = l_Lean_MessageData_hasTag(v___y_329_, v_a_339_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec_ref_known(v___x_345_, 1);
lean_dec_ref(v___x_343_);
lean_dec(v_a_339_);
v___x_348_ = lean_box(0);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_348_);
v___x_350_ = v___x_341_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_del_object(v___x_341_);
v___y_293_ = v___x_346_;
v___y_294_ = v___y_331_;
v___y_295_ = v___y_333_;
v___y_296_ = v___y_335_;
v___y_297_ = v_a_339_;
v___y_298_ = v___x_345_;
v___y_299_ = v___x_343_;
v___y_300_ = v___y_289_;
v___y_301_ = v___y_290_;
goto v___jp_292_;
}
}
}
}
v___jp_353_:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Syntax_getTailPos_x3f(v___y_360_, v___y_359_);
lean_dec(v___y_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_inc(v___y_361_);
v___y_329_ = v___y_354_;
v___y_330_ = v___y_355_;
v___y_331_ = v___y_356_;
v___y_332_ = v___y_358_;
v___y_333_ = v___y_357_;
v___y_334_ = v___y_361_;
v___y_335_ = v___y_359_;
v___y_336_ = v___y_361_;
goto v___jp_328_;
}
else
{
lean_object* v_val_363_; 
v_val_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v___x_362_, 1);
v___y_329_ = v___y_354_;
v___y_330_ = v___y_355_;
v___y_331_ = v___y_356_;
v___y_332_ = v___y_358_;
v___y_333_ = v___y_357_;
v___y_334_ = v___y_361_;
v___y_335_ = v___y_359_;
v___y_336_ = v_val_363_;
goto v___jp_328_;
}
}
v___jp_364_:
{
lean_object* v_ref_372_; lean_object* v___x_373_; 
v_ref_372_ = l_Lean_replaceRef(v_ref_283_, v___y_366_);
v___x_373_ = l_Lean_Syntax_getPos_x3f(v_ref_372_, v___y_370_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___y_354_ = v___y_365_;
v___y_355_ = v___y_367_;
v___y_356_ = v___y_371_;
v___y_357_ = v___y_369_;
v___y_358_ = v___y_368_;
v___y_359_ = v___y_370_;
v___y_360_ = v_ref_372_;
v___y_361_ = v___x_374_;
goto v___jp_353_;
}
else
{
lean_object* v_val_375_; 
v_val_375_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v___x_373_, 1);
v___y_354_ = v___y_365_;
v___y_355_ = v___y_367_;
v___y_356_ = v___y_371_;
v___y_357_ = v___y_369_;
v___y_358_ = v___y_368_;
v___y_359_ = v___y_370_;
v___y_360_ = v_ref_372_;
v___y_361_ = v_val_375_;
goto v___jp_353_;
}
}
v___jp_377_:
{
if (v___y_384_ == 0)
{
v___y_365_ = v___y_380_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_381_;
v___y_370_ = v___y_383_;
v___y_371_ = v_severity_285_;
goto v___jp_364_;
}
else
{
v___y_365_ = v___y_380_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_381_;
v___y_370_ = v___y_383_;
v___y_371_ = v___x_376_;
goto v___jp_364_;
}
}
v___jp_385_:
{
if (v___y_386_ == 0)
{
lean_object* v_fileName_387_; lean_object* v_fileMap_388_; lean_object* v_options_389_; lean_object* v_ref_390_; uint8_t v_suppressElabErrors_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___f_394_; uint8_t v___x_395_; uint8_t v___x_396_; 
v_fileName_387_ = lean_ctor_get(v___y_289_, 0);
v_fileMap_388_ = lean_ctor_get(v___y_289_, 1);
v_options_389_ = lean_ctor_get(v___y_289_, 2);
v_ref_390_ = lean_ctor_get(v___y_289_, 5);
v_suppressElabErrors_391_ = lean_ctor_get_uint8(v___y_289_, sizeof(void*)*14 + 1);
v___x_392_ = lean_box(v_suppressElabErrors_391_);
v___x_393_ = lean_box(v___y_386_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_394_, 0, v___x_392_);
lean_closure_set(v___f_394_, 1, v___x_393_);
v___x_395_ = 1;
v___x_396_ = l_Lean_instBEqMessageSeverity_beq(v_severity_285_, v___x_395_);
if (v___x_396_ == 0)
{
v___y_378_ = v_ref_390_;
v___y_379_ = v_fileMap_388_;
v___y_380_ = v___f_394_;
v___y_381_ = v_fileName_387_;
v___y_382_ = v_suppressElabErrors_391_;
v___y_383_ = v___y_386_;
v___y_384_ = v___x_396_;
goto v___jp_377_;
}
else
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = l_Lean_warningAsError;
v___x_398_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_389_, v___x_397_);
v___y_378_ = v_ref_390_;
v___y_379_ = v_fileMap_388_;
v___y_380_ = v___f_394_;
v___y_381_ = v_fileName_387_;
v___y_382_ = v_suppressElabErrors_391_;
v___y_383_ = v___y_386_;
v___y_384_ = v___x_398_;
goto v___jp_377_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_msgData_284_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___boxed(lean_object* v_ref_403_, lean_object* v_msgData_404_, lean_object* v_severity_405_, lean_object* v_isSilent_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_severity_boxed_412_; uint8_t v_isSilent_boxed_413_; lean_object* v_res_414_; 
v_severity_boxed_412_ = lean_unbox(v_severity_405_);
v_isSilent_boxed_413_ = lean_unbox(v_isSilent_406_);
v_res_414_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_403_, v_msgData_404_, v_severity_boxed_412_, v_isSilent_boxed_413_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v_ref_403_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(lean_object* v_msgData_415_, uint8_t v_severity_416_, uint8_t v_isSilent_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_ref_423_; lean_object* v___x_424_; 
v_ref_423_ = lean_ctor_get(v___y_420_, 5);
v___x_424_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44(v_ref_423_, v_msgData_415_, v_severity_416_, v_isSilent_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42___boxed(lean_object* v_msgData_425_, lean_object* v_severity_426_, lean_object* v_isSilent_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v_severity_boxed_433_; uint8_t v_isSilent_boxed_434_; lean_object* v_res_435_; 
v_severity_boxed_433_ = lean_unbox(v_severity_426_);
v_isSilent_boxed_434_ = lean_unbox(v_isSilent_427_);
v_res_435_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_425_, v_severity_boxed_433_, v_isSilent_boxed_434_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(lean_object* v_msgData_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = 1;
v___x_443_ = 0;
v___x_444_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42(v_msgData_436_, v___x_442_, v___x_443_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38___boxed(lean_object* v_msgData_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v_msgData_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(lean_object* v_opt_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_options_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_options_455_ = lean_ctor_get(v___y_453_, 2);
v___x_456_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_455_, v_opt_452_);
v___x_457_ = lean_box(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg___boxed(lean_object* v_opt_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_459_, v___y_460_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v_opt_459_);
return v_res_462_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__0));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__2));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(lean_object* v_id_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_498_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_478_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v___x_477_, v___y_472_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_498_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_498_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_498_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v_isExporting_488_; 
v_isExporting_488_ = lean_ctor_get_uint8(v_env_476_, sizeof(void*)*8);
lean_dec_ref(v_env_476_);
if (v_isExporting_488_ == 0)
{
lean_dec(v_a_479_);
lean_dec(v_id_469_);
goto v___jp_483_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l_Lean_isPrivateName(v_id_469_);
if (v___x_489_ == 0)
{
lean_dec(v_a_479_);
lean_dec(v_id_469_);
goto v___jp_483_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
if (v___x_490_ == 0)
{
lean_dec(v_id_469_);
goto v___jp_483_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_del_object(v___x_481_);
v___x_491_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_492_ = 0;
v___x_493_ = l_Lean_MessageData_ofConstName(v_id_469_, v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_491_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38(v___x_496_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_497_;
}
}
}
v___jp_483_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_box(0);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___boxed(lean_object* v_id_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_id_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(lean_object* v_x_506_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
return v___x_507_;
}
else
{
lean_object* v_head_508_; lean_object* v_tail_509_; lean_object* v_fst_510_; uint8_t v___x_511_; 
v_head_508_ = lean_ctor_get(v_x_506_, 0);
v_tail_509_ = lean_ctor_get(v_x_506_, 1);
v_fst_510_ = lean_ctor_get(v_head_508_, 0);
v___x_511_ = l_Lean_isPrivateName(v_fst_510_);
if (v___x_511_ == 0)
{
v_x_506_ = v_tail_509_;
goto _start;
}
else
{
lean_object* v___x_513_; 
lean_inc(v_head_508_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_head_508_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31___boxed(lean_object* v_x_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_x_514_);
lean_dec(v_x_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(lean_object* v_id_516_, uint8_t v_enableLog_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v_options_525_; lean_object* v_currNamespace_526_; lean_object* v_openDecls_527_; lean_object* v___x_528_; lean_object* v_env_529_; lean_object* v_res_530_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v_options_525_ = lean_ctor_get(v___y_520_, 2);
v_currNamespace_526_ = lean_ctor_get(v___y_520_, 6);
v_openDecls_527_ = lean_ctor_get(v___y_520_, 7);
v___x_528_ = lean_st_ref_get(v___y_521_);
v_env_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_env_529_);
lean_dec(v___x_528_);
lean_inc(v_openDecls_527_);
lean_inc(v_currNamespace_526_);
v_res_530_ = l_Lean_ResolveName_resolveGlobalName(v_env_524_, v_options_525_, v_currNamespace_526_, v_openDecls_527_, v_id_516_);
if (v_enableLog_517_ == 0)
{
lean_object* v___x_531_; 
lean_dec_ref(v_env_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_res_530_);
return v___x_531_;
}
else
{
uint8_t v_isExporting_532_; 
v_isExporting_532_ = lean_ctor_get_uint8(v_env_529_, sizeof(void*)*8);
lean_dec_ref(v_env_529_);
if (v_isExporting_532_ == 0)
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_res_530_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_530_);
if (lean_obj_tag(v___x_534_) == 1)
{
lean_object* v_val_535_; lean_object* v_fst_536_; lean_object* v___x_537_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_534_, 1);
v_fst_536_ = lean_ctor_get(v_val_535_, 0);
lean_inc(v_fst_536_);
lean_dec(v_val_535_);
v___x_537_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32(v_fst_536_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v___x_537_, 0);
lean_dec(v_unused_545_);
v___x_539_ = v___x_537_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_dec(v___x_537_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_res_530_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_res_530_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_res_530_);
v_a_546_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_537_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_537_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v___x_534_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_res_530_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26___boxed(lean_object* v_id_555_, lean_object* v_enableLog_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_enableLog_boxed_562_; lean_object* v_res_563_; 
v_enableLog_boxed_562_ = lean_unbox(v_enableLog_556_);
v_res_563_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_id_555_, v_enableLog_boxed_562_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(lean_object* v_view_564_, lean_object* v_findLocalDecl_x3f_565_, lean_object* v_n_566_, lean_object* v_projs_567_, uint8_t v_globalDeclFound_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___y_575_; lean_object* v___y_576_; uint8_t v_globalDeclFoundNext_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v_imported_584_; lean_object* v_ctx_585_; lean_object* v_scopes_586_; lean_object* v_givenNameView_587_; uint8_t v___y_589_; 
v_imported_584_ = lean_ctor_get(v_view_564_, 1);
v_ctx_585_ = lean_ctor_get(v_view_564_, 2);
v_scopes_586_ = lean_ctor_get(v_view_564_, 3);
lean_inc(v_scopes_586_);
lean_inc(v_ctx_585_);
lean_inc(v_imported_584_);
lean_inc(v_n_566_);
v_givenNameView_587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_587_, 0, v_n_566_);
lean_ctor_set(v_givenNameView_587_, 1, v_imported_584_);
lean_ctor_set(v_givenNameView_587_, 2, v_ctx_585_);
lean_ctor_set(v_givenNameView_587_, 3, v_scopes_586_);
if (v_globalDeclFound_568_ == 0)
{
v___y_589_ = v_globalDeclFound_568_;
goto v___jp_588_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = l_List_isEmpty___redArg(v_projs_567_);
if (v___x_624_ == 0)
{
v___y_589_ = v_globalDeclFound_568_;
goto v___jp_588_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
v___y_589_ = v___x_625_;
goto v___jp_588_;
}
}
v___jp_574_:
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_576_);
lean_ctor_set(v___x_582_, 1, v_projs_567_);
v_n_566_ = v___y_575_;
v_projs_567_ = v___x_582_;
v_globalDeclFound_568_ = v_globalDeclFoundNext_577_;
v___y_569_ = v___y_578_;
v___y_570_ = v___y_579_;
v___y_571_ = v___y_580_;
v___y_572_ = v___y_581_;
goto _start;
}
v___jp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(v___y_589_);
lean_inc_ref(v_findLocalDecl_x3f_565_);
lean_inc_ref(v_givenNameView_587_);
v___x_591_ = lean_apply_2(v_findLocalDecl_x3f_565_, v_givenNameView_587_, v___x_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
if (lean_obj_tag(v_n_566_) == 1)
{
if (v_globalDeclFound_568_ == 0)
{
lean_object* v_pre_592_; lean_object* v_str_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_pre_592_ = lean_ctor_get(v_n_566_, 0);
lean_inc(v_pre_592_);
v_str_593_ = lean_ctor_get(v_n_566_, 1);
lean_inc_ref(v_str_593_);
lean_dec_ref_known(v_n_566_, 2);
v___x_594_ = l_Lean_MacroScopesView_review(v_givenNameView_587_);
v___x_595_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v___x_594_, v_globalDeclFound_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v_r_598_; uint8_t v___x_599_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_box(0);
v_r_598_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__27(v_a_596_, v___x_597_);
v___x_599_ = l_List_isEmpty___redArg(v_r_598_);
lean_dec(v_r_598_);
if (v___x_599_ == 0)
{
uint8_t v_globalDeclFoundNext_600_; 
v_globalDeclFoundNext_600_ = 1;
v___y_575_ = v_pre_592_;
v___y_576_ = v_str_593_;
v_globalDeclFoundNext_577_ = v_globalDeclFoundNext_600_;
v___y_578_ = v___y_569_;
v___y_579_ = v___y_570_;
v___y_580_ = v___y_571_;
v___y_581_ = v___y_572_;
goto v___jp_574_;
}
else
{
v___y_575_ = v_pre_592_;
v___y_576_ = v_str_593_;
v_globalDeclFoundNext_577_ = v_globalDeclFound_568_;
v___y_578_ = v___y_569_;
v___y_579_ = v___y_570_;
v___y_580_ = v___y_571_;
v___y_581_ = v___y_572_;
goto v___jp_574_;
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_str_593_);
lean_dec(v_pre_592_);
lean_dec(v_projs_567_);
lean_dec_ref(v_findLocalDecl_x3f_565_);
v_a_601_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_595_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_595_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_pre_609_; lean_object* v_str_610_; 
lean_dec_ref_known(v_givenNameView_587_, 4);
v_pre_609_ = lean_ctor_get(v_n_566_, 0);
lean_inc(v_pre_609_);
v_str_610_ = lean_ctor_get(v_n_566_, 1);
lean_inc_ref(v_str_610_);
lean_dec_ref_known(v_n_566_, 2);
v___y_575_ = v_pre_609_;
v___y_576_ = v_str_610_;
v_globalDeclFoundNext_577_ = v_globalDeclFound_568_;
v___y_578_ = v___y_569_;
v___y_579_ = v___y_570_;
v___y_580_ = v___y_571_;
v___y_581_ = v___y_572_;
goto v___jp_574_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref_known(v_givenNameView_587_, 4);
lean_dec(v_projs_567_);
lean_dec(v_n_566_);
lean_dec_ref(v_findLocalDecl_x3f_565_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref_known(v_givenNameView_587_, 4);
lean_dec(v_n_566_);
lean_dec_ref(v_findLocalDecl_x3f_565_);
v_val_613_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_623_ == 0)
{
v___x_615_ = v___x_591_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v___x_591_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = l_Lean_LocalDecl_toExpr(v_val_613_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_projs_567_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_618_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20___boxed(lean_object* v_view_626_, lean_object* v_findLocalDecl_x3f_627_, lean_object* v_n_628_, lean_object* v_projs_629_, lean_object* v_globalDeclFound_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v_globalDeclFound_boxed_636_; lean_object* v_res_637_; 
v_globalDeclFound_boxed_636_ = lean_unbox(v_globalDeclFound_630_);
v_res_637_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_626_, v_findLocalDecl_x3f_627_, v_n_628_, v_projs_629_, v_globalDeclFound_boxed_636_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v_view_626_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(lean_object* v_t_638_, lean_object* v_k_639_){
_start:
{
if (lean_obj_tag(v_t_638_) == 0)
{
lean_object* v_k_640_; lean_object* v_v_641_; lean_object* v_l_642_; lean_object* v_r_643_; uint8_t v___x_644_; 
v_k_640_ = lean_ctor_get(v_t_638_, 1);
v_v_641_ = lean_ctor_get(v_t_638_, 2);
v_l_642_ = lean_ctor_get(v_t_638_, 3);
v_r_643_ = lean_ctor_get(v_t_638_, 4);
v___x_644_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_639_, v_k_640_);
switch(v___x_644_)
{
case 0:
{
v_t_638_ = v_l_642_;
goto _start;
}
case 1:
{
lean_object* v___x_646_; 
lean_inc(v_v_641_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_v_641_);
return v___x_646_;
}
default: 
{
v_t_638_ = v_r_643_;
goto _start;
}
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg___boxed(lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_649_, v_k_650_);
lean_dec(v_k_650_);
lean_dec(v_t_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(lean_object* v_localDecl_652_, lean_object* v_givenName_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = l_Lean_LocalDecl_userName(v_localDecl_652_);
v___x_655_ = lean_name_eq(v___x_654_, v_givenName_653_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_localDecl_652_);
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_localDecl_652_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0___boxed(lean_object* v_localDecl_658_, lean_object* v_givenName_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_localDecl_658_, v_givenName_659_);
lean_dec(v_givenName_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(lean_object* v_givenName_661_, uint8_t v_skipAuxDecl_662_, lean_object* v_auxDeclToFullName_663_, lean_object* v___x_664_, lean_object* v_givenNameView_665_, lean_object* v_as_666_, lean_object* v_i_667_){
_start:
{
lean_object* v_zero_668_; uint8_t v_isZero_669_; 
v_zero_668_ = lean_unsigned_to_nat(0u);
v_isZero_669_ = lean_nat_dec_eq(v_i_667_, v_zero_668_);
if (v_isZero_669_ == 1)
{
lean_object* v___x_670_; 
lean_dec(v_i_667_);
lean_dec_ref(v_givenNameView_665_);
lean_dec(v___x_664_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_one_671_; lean_object* v_n_672_; lean_object* v___y_674_; lean_object* v___x_676_; 
v_one_671_ = lean_unsigned_to_nat(1u);
v_n_672_ = lean_nat_sub(v_i_667_, v_one_671_);
lean_dec(v_i_667_);
v___x_676_ = lean_array_fget_borrowed(v_as_666_, v_n_672_);
if (lean_obj_tag(v___x_676_) == 0)
{
v___y_674_ = v___x_676_;
goto v___jp_673_;
}
else
{
lean_object* v_val_677_; uint8_t v___x_678_; 
v_val_677_ = lean_ctor_get(v___x_676_, 0);
v___x_678_ = l_Lean_LocalDecl_isAuxDecl(v_val_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_inc(v_val_677_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_677_, v_givenName_661_);
v___y_674_ = v___x_679_;
goto v___jp_673_;
}
else
{
if (v_skipAuxDecl_662_ == 0)
{
if (v___x_678_ == 0)
{
v_i_667_ = v_n_672_;
goto _start;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lean_LocalDecl_fvarId(v_val_677_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_auxDeclToFullName_663_, v___x_681_);
lean_dec(v___x_681_);
if (lean_obj_tag(v___x_682_) == 1)
{
lean_object* v_val_683_; lean_object* v_fullDeclView_684_; lean_object* v___y_686_; lean_object* v_name_707_; lean_object* v___x_708_; 
v_val_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_682_, 1);
v_fullDeclView_684_ = l_Lean_extractMacroScopes(v_val_683_);
v_name_707_ = lean_ctor_get(v_fullDeclView_684_, 0);
lean_inc_n(v_name_707_, 2);
v___x_708_ = l_Lean_privateToUserName_x3f(v_name_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
v___y_686_ = v_name_707_;
goto v___jp_685_;
}
else
{
lean_object* v_val_709_; 
lean_dec(v_name_707_);
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_708_, 1);
v___y_686_ = v_val_709_;
goto v___jp_685_;
}
v___jp_685_:
{
lean_object* v_imported_687_; lean_object* v_ctx_688_; lean_object* v_scopes_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_705_; 
v_imported_687_ = lean_ctor_get(v_fullDeclView_684_, 1);
v_ctx_688_ = lean_ctor_get(v_fullDeclView_684_, 2);
v_scopes_689_ = lean_ctor_get(v_fullDeclView_684_, 3);
v_isSharedCheck_705_ = !lean_is_exclusive(v_fullDeclView_684_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_fullDeclView_684_, 0);
lean_dec(v_unused_706_);
v___x_691_ = v_fullDeclView_684_;
v_isShared_692_ = v_isSharedCheck_705_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_scopes_689_);
lean_inc(v_ctx_688_);
lean_inc(v_imported_687_);
lean_dec(v_fullDeclView_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_705_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fullDeclView_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___y_686_);
v_fullDeclView_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___y_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_imported_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ctx_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_scopes_689_);
v_fullDeclView_694_ = v_reuseFailAlloc_704_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v_fullDeclName_695_; uint8_t v___x_696_; 
lean_inc_ref(v_fullDeclView_694_);
v_fullDeclName_695_ = l_Lean_MacroScopesView_review(v_fullDeclView_694_);
v___x_696_ = l_Lean_Name_isPrefixOf(v___x_664_, v_fullDeclName_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_dec_ref(v_fullDeclView_694_);
lean_inc(v___x_664_);
lean_inc_ref(v_givenNameView_665_);
lean_inc(v_val_677_);
v___x_697_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_677_, v_givenNameView_665_, v_fullDeclName_695_, v___x_664_);
lean_dec(v_fullDeclName_695_);
v___y_674_ = v___x_697_;
goto v___jp_673_;
}
else
{
lean_object* v___x_698_; lean_object* v_localDeclNameView_699_; uint8_t v___x_700_; 
lean_dec(v_fullDeclName_695_);
v___x_698_ = l_Lean_LocalDecl_userName(v_val_677_);
v_localDeclNameView_699_ = l_Lean_extractMacroScopes(v___x_698_);
v___x_700_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_699_, v_givenNameView_665_);
lean_dec_ref(v_localDeclNameView_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v_fullDeclView_694_);
v_i_667_ = v_n_672_;
goto _start;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_665_, v_fullDeclView_694_);
lean_dec_ref(v_fullDeclView_694_);
if (v___x_702_ == 0)
{
v_i_667_ = v_n_672_;
goto _start;
}
else
{
lean_inc_ref(v___x_676_);
v___y_674_ = v___x_676_;
goto v___jp_673_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v___x_682_);
lean_inc(v_val_677_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___lam__0(v_val_677_, v_givenName_661_);
v___y_674_ = v___x_710_;
goto v___jp_673_;
}
}
}
else
{
v_i_667_ = v_n_672_;
goto _start;
}
}
}
v___jp_673_:
{
if (lean_obj_tag(v___y_674_) == 0)
{
v_i_667_ = v_n_672_;
goto _start;
}
else
{
lean_dec(v_n_672_);
lean_dec_ref(v_givenNameView_665_);
lean_dec(v___x_664_);
return v___y_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg___boxed(lean_object* v_givenName_712_, lean_object* v_skipAuxDecl_713_, lean_object* v_auxDeclToFullName_714_, lean_object* v___x_715_, lean_object* v_givenNameView_716_, lean_object* v_as_717_, lean_object* v_i_718_){
_start:
{
uint8_t v_skipAuxDecl_boxed_719_; lean_object* v_res_720_; 
v_skipAuxDecl_boxed_719_ = lean_unbox(v_skipAuxDecl_713_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_712_, v_skipAuxDecl_boxed_719_, v_auxDeclToFullName_714_, v___x_715_, v_givenNameView_716_, v_as_717_, v_i_718_);
lean_dec_ref(v_as_717_);
lean_dec(v_auxDeclToFullName_714_);
lean_dec(v_givenName_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(lean_object* v_givenName_721_, uint8_t v_skipAuxDecl_722_, lean_object* v_auxDeclToFullName_723_, lean_object* v___x_724_, lean_object* v_givenNameView_725_, lean_object* v_as_726_, lean_object* v_i_727_){
_start:
{
lean_object* v_zero_728_; uint8_t v_isZero_729_; 
v_zero_728_ = lean_unsigned_to_nat(0u);
v_isZero_729_ = lean_nat_dec_eq(v_i_727_, v_zero_728_);
if (v_isZero_729_ == 1)
{
lean_object* v___x_730_; 
lean_dec(v_i_727_);
lean_dec_ref(v_givenNameView_725_);
lean_dec(v___x_724_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v_one_731_; lean_object* v_n_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_one_731_ = lean_unsigned_to_nat(1u);
v_n_732_ = lean_nat_sub(v_i_727_, v_one_731_);
lean_dec(v_i_727_);
v___x_733_ = lean_array_fget_borrowed(v_as_726_, v_n_732_);
lean_inc_ref(v_givenNameView_725_);
lean_inc(v___x_724_);
v___x_734_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_721_, v_skipAuxDecl_722_, v_auxDeclToFullName_723_, v___x_724_, v_givenNameView_725_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
v_i_727_ = v_n_732_;
goto _start;
}
else
{
lean_dec(v_n_732_);
lean_dec_ref(v_givenNameView_725_);
lean_dec(v___x_724_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(lean_object* v_givenName_736_, uint8_t v_skipAuxDecl_737_, lean_object* v_auxDeclToFullName_738_, lean_object* v___x_739_, lean_object* v_givenNameView_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v_cs_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_cs_742_ = lean_ctor_get(v_x_741_, 0);
v___x_743_ = lean_array_get_size(v_cs_742_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_736_, v_skipAuxDecl_737_, v_auxDeclToFullName_738_, v___x_739_, v_givenNameView_740_, v_cs_742_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_vs_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_vs_745_ = lean_ctor_get(v_x_741_, 0);
v___x_746_ = lean_array_get_size(v_vs_745_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_736_, v_skipAuxDecl_737_, v_auxDeclToFullName_738_, v___x_739_, v_givenNameView_740_, v_vs_745_, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21___boxed(lean_object* v_givenName_748_, lean_object* v_skipAuxDecl_749_, lean_object* v_auxDeclToFullName_750_, lean_object* v___x_751_, lean_object* v_givenNameView_752_, lean_object* v_x_753_){
_start:
{
uint8_t v_skipAuxDecl_boxed_754_; lean_object* v_res_755_; 
v_skipAuxDecl_boxed_754_ = lean_unbox(v_skipAuxDecl_749_);
v_res_755_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_748_, v_skipAuxDecl_boxed_754_, v_auxDeclToFullName_750_, v___x_751_, v_givenNameView_752_, v_x_753_);
lean_dec_ref(v_x_753_);
lean_dec(v_auxDeclToFullName_750_);
lean_dec(v_givenName_748_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg___boxed(lean_object* v_givenName_756_, lean_object* v_skipAuxDecl_757_, lean_object* v_auxDeclToFullName_758_, lean_object* v___x_759_, lean_object* v_givenNameView_760_, lean_object* v_as_761_, lean_object* v_i_762_){
_start:
{
uint8_t v_skipAuxDecl_boxed_763_; lean_object* v_res_764_; 
v_skipAuxDecl_boxed_763_ = lean_unbox(v_skipAuxDecl_757_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_756_, v_skipAuxDecl_boxed_763_, v_auxDeclToFullName_758_, v___x_759_, v_givenNameView_760_, v_as_761_, v_i_762_);
lean_dec_ref(v_as_761_);
lean_dec(v_auxDeclToFullName_758_);
lean_dec(v_givenName_756_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(lean_object* v_givenName_765_, uint8_t v_skipAuxDecl_766_, lean_object* v_auxDeclToFullName_767_, lean_object* v___x_768_, lean_object* v_givenNameView_769_, lean_object* v_t_770_){
_start:
{
lean_object* v_root_771_; lean_object* v_tail_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_root_771_ = lean_ctor_get(v_t_770_, 0);
v_tail_772_ = lean_ctor_get(v_t_770_, 1);
v___x_773_ = lean_array_get_size(v_tail_772_);
lean_inc_ref(v_givenNameView_769_);
lean_inc(v___x_768_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_765_, v_skipAuxDecl_766_, v_auxDeclToFullName_767_, v___x_768_, v_givenNameView_769_, v_tail_772_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21(v_givenName_765_, v_skipAuxDecl_766_, v_auxDeclToFullName_767_, v___x_768_, v_givenNameView_769_, v_root_771_);
return v___x_775_;
}
else
{
lean_dec_ref(v_givenNameView_769_);
lean_dec(v___x_768_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18___boxed(lean_object* v_givenName_776_, lean_object* v_skipAuxDecl_777_, lean_object* v_auxDeclToFullName_778_, lean_object* v___x_779_, lean_object* v_givenNameView_780_, lean_object* v_t_781_){
_start:
{
uint8_t v_skipAuxDecl_boxed_782_; lean_object* v_res_783_; 
v_skipAuxDecl_boxed_782_ = lean_unbox(v_skipAuxDecl_777_);
v_res_783_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_776_, v_skipAuxDecl_boxed_782_, v_auxDeclToFullName_778_, v___x_779_, v_givenNameView_780_, v_t_781_);
lean_dec_ref(v_t_781_);
lean_dec(v_auxDeclToFullName_778_);
lean_dec(v_givenName_776_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(lean_object* v_localDecl_x3f_784_, lean_object* v_givenName_785_, lean_object* v_as_786_, lean_object* v_i_787_){
_start:
{
lean_object* v_zero_788_; uint8_t v_isZero_789_; 
v_zero_788_ = lean_unsigned_to_nat(0u);
v_isZero_789_ = lean_nat_dec_eq(v_i_787_, v_zero_788_);
if (v_isZero_789_ == 1)
{
lean_object* v___x_790_; 
lean_dec(v_i_787_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v_one_791_; lean_object* v_n_792_; lean_object* v___y_794_; lean_object* v___x_796_; 
v_one_791_ = lean_unsigned_to_nat(1u);
v_n_792_ = lean_nat_sub(v_i_787_, v_one_791_);
lean_dec(v_i_787_);
v___x_796_ = lean_array_fget_borrowed(v_as_786_, v_n_792_);
if (lean_obj_tag(v___x_796_) == 0)
{
v___y_794_ = v___x_796_;
goto v___jp_793_;
}
else
{
lean_object* v_val_797_; uint8_t v___x_798_; 
v_val_797_ = lean_ctor_get(v___x_796_, 0);
v___x_798_ = l_Lean_LocalDecl_isAuxDecl(v_val_797_);
if (v___x_798_ == 0)
{
v___y_794_ = v_localDecl_x3f_784_;
goto v___jp_793_;
}
else
{
lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_799_ = l_Lean_LocalDecl_userName(v_val_797_);
v___x_800_ = lean_name_eq(v___x_799_, v_givenName_785_);
lean_dec(v___x_799_);
if (v___x_800_ == 0)
{
v_i_787_ = v_n_792_;
goto _start;
}
else
{
v___y_794_ = v___x_796_;
goto v___jp_793_;
}
}
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
v_i_787_ = v_n_792_;
goto _start;
}
else
{
lean_dec(v_n_792_);
lean_inc_ref(v___y_794_);
return v___y_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg___boxed(lean_object* v_localDecl_x3f_802_, lean_object* v_givenName_803_, lean_object* v_as_804_, lean_object* v_i_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_802_, v_givenName_803_, v_as_804_, v_i_805_);
lean_dec_ref(v_as_804_);
lean_dec(v_givenName_803_);
lean_dec(v_localDecl_x3f_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(lean_object* v_localDecl_x3f_807_, lean_object* v_givenName_808_, lean_object* v_as_809_, lean_object* v_i_810_){
_start:
{
lean_object* v_zero_811_; uint8_t v_isZero_812_; 
v_zero_811_ = lean_unsigned_to_nat(0u);
v_isZero_812_ = lean_nat_dec_eq(v_i_810_, v_zero_811_);
if (v_isZero_812_ == 1)
{
lean_object* v___x_813_; 
lean_dec(v_i_810_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v_one_814_; lean_object* v_n_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_one_814_ = lean_unsigned_to_nat(1u);
v_n_815_ = lean_nat_sub(v_i_810_, v_one_814_);
lean_dec(v_i_810_);
v___x_816_ = lean_array_fget_borrowed(v_as_809_, v_n_815_);
v___x_817_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_807_, v_givenName_808_, v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
v_i_810_ = v_n_815_;
goto _start;
}
else
{
lean_dec(v_n_815_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(lean_object* v_localDecl_x3f_819_, lean_object* v_givenName_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v_cs_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_cs_822_ = lean_ctor_get(v_x_821_, 0);
v___x_823_ = lean_array_get_size(v_cs_822_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_819_, v_givenName_820_, v_cs_822_, v___x_823_);
return v___x_824_;
}
else
{
lean_object* v_vs_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_vs_825_ = lean_ctor_get(v_x_821_, 0);
v___x_826_ = lean_array_get_size(v_vs_825_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_819_, v_givenName_820_, v_vs_825_, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_localDecl_x3f_828_, lean_object* v_givenName_829_, lean_object* v_x_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_828_, v_givenName_829_, v_x_830_);
lean_dec_ref(v_x_830_);
lean_dec(v_givenName_829_);
lean_dec(v_localDecl_x3f_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg___boxed(lean_object* v_localDecl_x3f_832_, lean_object* v_givenName_833_, lean_object* v_as_834_, lean_object* v_i_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_832_, v_givenName_833_, v_as_834_, v_i_835_);
lean_dec_ref(v_as_834_);
lean_dec(v_givenName_833_);
lean_dec(v_localDecl_x3f_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(lean_object* v_localDecl_x3f_837_, lean_object* v_givenName_838_, lean_object* v_t_839_){
_start:
{
lean_object* v_root_840_; lean_object* v_tail_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_root_840_ = lean_ctor_get(v_t_839_, 0);
v_tail_841_ = lean_ctor_get(v_t_839_, 1);
v___x_842_ = lean_array_get_size(v_tail_841_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_837_, v_givenName_838_, v_tail_841_, v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24(v_localDecl_x3f_837_, v_givenName_838_, v_root_840_);
return v___x_844_;
}
else
{
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19___boxed(lean_object* v_localDecl_x3f_845_, lean_object* v_givenName_846_, lean_object* v_t_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_845_, v_givenName_846_, v_t_847_);
lean_dec_ref(v_t_847_);
lean_dec(v_givenName_846_);
lean_dec(v_localDecl_x3f_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(lean_object* v_auxDeclToFullName_849_, lean_object* v_currNamespace_850_, lean_object* v_decls_851_, lean_object* v_givenNameView_852_, uint8_t v_skipAuxDecl_853_){
_start:
{
lean_object* v_givenName_854_; lean_object* v_localDecl_x3f_855_; 
lean_inc_ref(v_givenNameView_852_);
v_givenName_854_ = l_Lean_MacroScopesView_review(v_givenNameView_852_);
v_localDecl_x3f_855_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18(v_givenName_854_, v_skipAuxDecl_853_, v_auxDeclToFullName_849_, v_currNamespace_850_, v_givenNameView_852_, v_decls_851_);
if (lean_obj_tag(v_localDecl_x3f_855_) == 0)
{
if (v_skipAuxDecl_853_ == 0)
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19(v_localDecl_x3f_855_, v_givenName_854_, v_decls_851_);
lean_dec(v_givenName_854_);
return v___x_856_;
}
else
{
lean_dec(v_givenName_854_);
return v_localDecl_x3f_855_;
}
}
else
{
lean_dec(v_givenName_854_);
return v_localDecl_x3f_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed(lean_object* v_auxDeclToFullName_857_, lean_object* v_currNamespace_858_, lean_object* v_decls_859_, lean_object* v_givenNameView_860_, lean_object* v_skipAuxDecl_861_){
_start:
{
uint8_t v_skipAuxDecl_boxed_862_; lean_object* v_res_863_; 
v_skipAuxDecl_boxed_862_ = lean_unbox(v_skipAuxDecl_861_);
v_res_863_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0(v_auxDeclToFullName_857_, v_currNamespace_858_, v_decls_859_, v_givenNameView_860_, v_skipAuxDecl_boxed_862_);
lean_dec_ref(v_decls_859_);
lean_dec(v_auxDeclToFullName_857_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(lean_object* v_n_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_lctx_870_; lean_object* v_decls_871_; lean_object* v_auxDeclToFullName_872_; lean_object* v_currNamespace_873_; lean_object* v_view_874_; lean_object* v_name_875_; lean_object* v_findLocalDecl_x3f_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; 
v_lctx_870_ = lean_ctor_get(v___y_865_, 2);
v_decls_871_ = lean_ctor_get(v_lctx_870_, 1);
v_auxDeclToFullName_872_ = lean_ctor_get(v_lctx_870_, 2);
v_currNamespace_873_ = lean_ctor_get(v___y_867_, 6);
v_view_874_ = l_Lean_extractMacroScopes(v_n_864_);
v_name_875_ = lean_ctor_get(v_view_874_, 0);
lean_inc(v_name_875_);
lean_inc_ref(v_decls_871_);
lean_inc(v_currNamespace_873_);
lean_inc(v_auxDeclToFullName_872_);
v_findLocalDecl_x3f_876_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_876_, 0, v_auxDeclToFullName_872_);
lean_closure_set(v_findLocalDecl_x3f_876_, 1, v_currNamespace_873_);
lean_closure_set(v_findLocalDecl_x3f_876_, 2, v_decls_871_);
v___x_877_ = lean_box(0);
v___x_878_ = 0;
v___x_879_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20(v_view_874_, v_findLocalDecl_x3f_876_, v_name_875_, v___x_877_, v___x_878_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_view_874_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11___boxed(lean_object* v_n_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(uint8_t v___x_887_, lean_object* v_n_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11(v_n_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_908_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_908_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_908_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_908_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 0)
{
uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_899_ = 1;
v___x_900_ = lean_box(v___x_899_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec_ref_known(v_a_895_, 1);
v___x_904_ = lean_box(v___x_887_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_904_);
v___x_906_ = v___x_897_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_894_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_894_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0___boxed(lean_object* v___x_917_, lean_object* v_n_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_43669__boxed_924_; lean_object* v_res_925_; 
v___x_43669__boxed_924_ = lean_unbox(v___x_917_);
v_res_925_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___lam__0(v___x_43669__boxed_924_, v_n_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(lean_object* v___x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_926_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0___boxed(lean_object* v___x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___lam__0(v___x_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(lean_object* v_opt_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_options_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_options_943_ = lean_ctor_get(v___y_941_, 2);
v___x_944_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_943_, v_opt_940_);
v___x_945_ = lean_box(v___x_944_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg___boxed(lean_object* v_opt_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_948_, v___y_949_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_opt_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(lean_object* v_ref_954_, lean_object* v_msgData_955_, uint8_t v_severity_956_, uint8_t v_isSilent_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_a_964_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_1003_; lean_object* v___y_1004_; uint8_t v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; uint8_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1030_; uint8_t v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; uint8_t v___x_1049_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; uint8_t v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1059_; uint8_t v___x_1074_; 
v___x_1049_ = 2;
v___x_1074_ = l_Lean_instBEqMessageSeverity_beq(v_severity_956_, v___x_1049_);
if (v___x_1074_ == 0)
{
v___y_1059_ = v___x_1074_;
goto v___jp_1058_;
}
else
{
uint8_t v___x_1075_; 
lean_inc_ref(v_msgData_955_);
v___x_1075_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_955_);
v___y_1059_ = v___x_1075_;
goto v___jp_1058_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_a_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
v___jp_967_:
{
lean_object* v___x_977_; lean_object* v_currNamespace_978_; lean_object* v_openDecls_979_; lean_object* v_env_980_; lean_object* v_nextMacroScope_981_; lean_object* v_ngen_982_; lean_object* v_auxDeclNGen_983_; lean_object* v_traceState_984_; lean_object* v_cache_985_; lean_object* v_messages_986_; lean_object* v_infoState_987_; lean_object* v_snapshotTasks_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1001_; 
v___x_977_ = lean_st_ref_take(v___y_976_);
v_currNamespace_978_ = lean_ctor_get(v___y_975_, 6);
v_openDecls_979_ = lean_ctor_get(v___y_975_, 7);
v_env_980_ = lean_ctor_get(v___x_977_, 0);
v_nextMacroScope_981_ = lean_ctor_get(v___x_977_, 1);
v_ngen_982_ = lean_ctor_get(v___x_977_, 2);
v_auxDeclNGen_983_ = lean_ctor_get(v___x_977_, 3);
v_traceState_984_ = lean_ctor_get(v___x_977_, 4);
v_cache_985_ = lean_ctor_get(v___x_977_, 5);
v_messages_986_ = lean_ctor_get(v___x_977_, 6);
v_infoState_987_ = lean_ctor_get(v___x_977_, 7);
v_snapshotTasks_988_ = lean_ctor_get(v___x_977_, 8);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_990_ = v___x_977_;
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snapshotTasks_988_);
lean_inc(v_infoState_987_);
lean_inc(v_messages_986_);
lean_inc(v_cache_985_);
lean_inc(v_traceState_984_);
lean_inc(v_auxDeclNGen_983_);
lean_inc(v_ngen_982_);
lean_inc(v_nextMacroScope_981_);
lean_inc(v_env_980_);
lean_dec(v___x_977_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_openDecls_979_);
lean_inc(v_currNamespace_978_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_currNamespace_978_);
lean_ctor_set(v___x_992_, 1, v_openDecls_979_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_969_);
lean_inc_ref(v___y_970_);
lean_inc_ref(v___y_968_);
v___x_994_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_994_, 0, v___y_968_);
lean_ctor_set(v___x_994_, 1, v___y_972_);
lean_ctor_set(v___x_994_, 2, v___y_971_);
lean_ctor_set(v___x_994_, 3, v___y_970_);
lean_ctor_set(v___x_994_, 4, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5, v___y_974_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 1, v___y_973_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 2, v_isSilent_957_);
v___x_995_ = l_Lean_MessageLog_add(v___x_994_, v_messages_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 6, v___x_995_);
v___x_997_ = v___x_990_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_env_980_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_nextMacroScope_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_ngen_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_auxDeclNGen_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_traceState_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v_cache_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_infoState_987_);
lean_ctor_set(v_reuseFailAlloc_1000_, 8, v_snapshotTasks_988_);
v___x_997_ = v_reuseFailAlloc_1000_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_st_ref_put(v___y_976_, v___x_997_);
v___x_999_ = lean_box(0);
v_a_964_ = v___x_999_;
goto v___jp_963_;
}
}
}
v___jp_1002_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1025_; 
v___x_1011_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_955_);
v___x_1012_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44_spec__47(v___x_1011_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1025_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc_ref_n(v___y_1009_, 2);
v___x_1017_ = l_Lean_FileMap_toPosition(v___y_1009_, v___y_1006_);
lean_dec(v___y_1006_);
v___x_1018_ = l_Lean_FileMap_toPosition(v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1018_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1005_ == 0)
{
lean_dec_ref(v___y_1003_);
v___y_968_ = v___y_1004_;
v___y_969_ = v_a_1013_;
v___y_970_ = v___x_1021_;
v___y_971_ = v___x_1020_;
v___y_972_ = v___x_1017_;
v___y_973_ = v___y_1008_;
v___y_974_ = v___y_1007_;
v___y_975_ = v___y_960_;
v___y_976_ = v___y_961_;
goto v___jp_967_;
}
else
{
uint8_t v___x_1022_; 
lean_inc(v_a_1013_);
v___x_1022_ = l_Lean_MessageData_hasTag(v___y_1003_, v_a_1013_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1017_);
lean_dec(v_a_1013_);
v___x_1023_ = lean_box(0);
v_a_964_ = v___x_1023_;
goto v___jp_963_;
}
else
{
v___y_968_ = v___y_1004_;
v___y_969_ = v_a_1013_;
v___y_970_ = v___x_1021_;
v___y_971_ = v___x_1020_;
v___y_972_ = v___x_1017_;
v___y_973_ = v___y_1008_;
v___y_974_ = v___y_1007_;
v___y_975_ = v___y_960_;
v___y_976_ = v___y_961_;
goto v___jp_967_;
}
}
}
}
}
v___jp_1026_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Syntax_getTailPos_x3f(v___y_1028_, v___y_1032_);
lean_dec(v___y_1028_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_inc(v___y_1034_);
v___y_1003_ = v___y_1027_;
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v___y_1034_;
v___y_1007_ = v___y_1032_;
v___y_1008_ = v___y_1031_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v___y_1034_;
goto v___jp_1002_;
}
else
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___y_1003_ = v___y_1027_;
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v___y_1034_;
v___y_1007_ = v___y_1032_;
v___y_1008_ = v___y_1031_;
v___y_1009_ = v___y_1033_;
v___y_1010_ = v_val_1036_;
goto v___jp_1002_;
}
}
v___jp_1037_:
{
lean_object* v_ref_1045_; lean_object* v___x_1046_; 
v_ref_1045_ = l_Lean_replaceRef(v_ref_954_, v___y_1043_);
v___x_1046_ = l_Lean_Syntax_getPos_x3f(v_ref_1045_, v___y_1041_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___y_1027_ = v___y_1038_;
v___y_1028_ = v_ref_1045_;
v___y_1029_ = v___y_1039_;
v___y_1030_ = v___y_1040_;
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1041_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v___x_1047_;
goto v___jp_1026_;
}
else
{
lean_object* v_val_1048_; 
v_val_1048_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___x_1046_, 1);
v___y_1027_ = v___y_1038_;
v___y_1028_ = v_ref_1045_;
v___y_1029_ = v___y_1039_;
v___y_1030_ = v___y_1040_;
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1041_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v_val_1048_;
goto v___jp_1026_;
}
}
v___jp_1050_:
{
if (v___y_1057_ == 0)
{
v___y_1038_ = v___y_1053_;
v___y_1039_ = v___y_1051_;
v___y_1040_ = v___y_1052_;
v___y_1041_ = v___y_1056_;
v___y_1042_ = v___y_1055_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v_severity_956_;
goto v___jp_1037_;
}
else
{
v___y_1038_ = v___y_1053_;
v___y_1039_ = v___y_1051_;
v___y_1040_ = v___y_1052_;
v___y_1041_ = v___y_1056_;
v___y_1042_ = v___y_1055_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___x_1049_;
goto v___jp_1037_;
}
}
v___jp_1058_:
{
if (v___y_1059_ == 0)
{
lean_object* v_fileName_1060_; lean_object* v_fileMap_1061_; lean_object* v_options_1062_; lean_object* v_ref_1063_; uint8_t v_suppressElabErrors_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; uint8_t v___x_1068_; uint8_t v___x_1069_; 
v_fileName_1060_ = lean_ctor_get(v___y_960_, 0);
v_fileMap_1061_ = lean_ctor_get(v___y_960_, 1);
v_options_1062_ = lean_ctor_get(v___y_960_, 2);
v_ref_1063_ = lean_ctor_get(v___y_960_, 5);
v_suppressElabErrors_1064_ = lean_ctor_get_uint8(v___y_960_, sizeof(void*)*14 + 1);
v___x_1065_ = lean_box(v_suppressElabErrors_1064_);
v___x_1066_ = lean_box(v___y_1059_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1067_, 0, v___x_1065_);
lean_closure_set(v___f_1067_, 1, v___x_1066_);
v___x_1068_ = 1;
v___x_1069_ = l_Lean_instBEqMessageSeverity_beq(v_severity_956_, v___x_1068_);
if (v___x_1069_ == 0)
{
v___y_1051_ = v_fileName_1060_;
v___y_1052_ = v_suppressElabErrors_1064_;
v___y_1053_ = v___f_1067_;
v___y_1054_ = v_ref_1063_;
v___y_1055_ = v_fileMap_1061_;
v___y_1056_ = v___y_1059_;
v___y_1057_ = v___x_1069_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = l_Lean_warningAsError;
v___x_1071_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_1062_, v___x_1070_);
v___y_1051_ = v_fileName_1060_;
v___y_1052_ = v_suppressElabErrors_1064_;
v___y_1053_ = v___f_1067_;
v___y_1054_ = v_ref_1063_;
v___y_1055_ = v_fileMap_1061_;
v___y_1056_ = v___y_1059_;
v___y_1057_ = v___x_1071_;
goto v___jp_1050_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v_msgData_955_);
v___x_1072_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___boxed(lean_object* v_ref_1076_, lean_object* v_msgData_1077_, lean_object* v_severity_1078_, lean_object* v_isSilent_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v_severity_boxed_1085_; uint8_t v_isSilent_boxed_1086_; lean_object* v_res_1087_; 
v_severity_boxed_1085_ = lean_unbox(v_severity_1078_);
v_isSilent_boxed_1086_ = lean_unbox(v_isSilent_1079_);
v_res_1087_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1076_, v_msgData_1077_, v_severity_boxed_1085_, v_isSilent_boxed_1086_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_ref_1076_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(lean_object* v_msgData_1088_, uint8_t v_severity_1089_, uint8_t v_isSilent_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_ref_1096_; lean_object* v___x_1097_; 
v_ref_1096_ = lean_ctor_get(v___y_1093_, 5);
v___x_1097_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48(v_ref_1096_, v_msgData_1088_, v_severity_1089_, v_isSilent_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46___boxed(lean_object* v_msgData_1098_, lean_object* v_severity_1099_, lean_object* v_isSilent_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_severity_boxed_1106_; uint8_t v_isSilent_boxed_1107_; lean_object* v_res_1108_; 
v_severity_boxed_1106_ = lean_unbox(v_severity_1099_);
v_isSilent_boxed_1107_ = lean_unbox(v_isSilent_1100_);
v_res_1108_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1098_, v_severity_boxed_1106_, v_isSilent_boxed_1107_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(lean_object* v_msgData_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = 1;
v___x_1116_ = 0;
v___x_1117_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46(v_msgData_1109_, v___x_1115_, v___x_1116_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v_msgData_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(lean_object* v_id_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_env_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1155_; 
v___x_1131_ = lean_st_ref_get(v___y_1129_);
v_env_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_env_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1134_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v___x_1133_, v___y_1128_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v_isExporting_1144_; 
v_isExporting_1144_ = lean_ctor_get_uint8(v_env_1132_, sizeof(void*)*8);
lean_dec_ref(v_env_1132_);
if (v_isExporting_1144_ == 0)
{
lean_dec(v_a_1135_);
lean_dec(v_id_1125_);
goto v___jp_1139_;
}
else
{
lean_object* v_val_1145_; uint8_t v___x_1146_; 
v_val_1145_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_val_1145_);
lean_dec(v_a_1135_);
v___x_1146_ = l_Lean_isPrivateName(v_id_1125_);
if (v___x_1146_ == 0)
{
lean_dec(v_val_1145_);
lean_dec(v_id_1125_);
goto v___jp_1139_;
}
else
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_unbox(v_val_1145_);
lean_dec(v_val_1145_);
if (v___x_1147_ == 0)
{
lean_dec(v_id_1125_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_del_object(v___x_1137_);
v___x_1148_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__1);
v___x_1149_ = 0;
v___x_1150_ = l_Lean_MessageData_ofConstName(v_id_1125_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32___closed__3);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44(v___x_1153_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1154_;
}
}
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__44_spec__46_spec__48___closed__0));
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40___boxed(lean_object* v_id_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_id_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(lean_object* v_id_1163_, uint8_t v_enableLog_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v_env_1171_; lean_object* v_options_1172_; lean_object* v_currNamespace_1173_; lean_object* v_openDecls_1174_; lean_object* v___x_1175_; lean_object* v_env_1176_; lean_object* v_res_1177_; 
v___x_1170_ = lean_st_ref_get(v___y_1168_);
v_env_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc_ref(v_env_1171_);
lean_dec(v___x_1170_);
v_options_1172_ = lean_ctor_get(v___y_1167_, 2);
v_currNamespace_1173_ = lean_ctor_get(v___y_1167_, 6);
v_openDecls_1174_ = lean_ctor_get(v___y_1167_, 7);
v___x_1175_ = lean_st_ref_get(v___y_1168_);
v_env_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_ref(v_env_1176_);
lean_dec(v___x_1175_);
lean_inc(v_openDecls_1174_);
lean_inc(v_currNamespace_1173_);
v_res_1177_ = l_Lean_ResolveName_resolveGlobalName(v_env_1171_, v_options_1172_, v_currNamespace_1173_, v_openDecls_1174_, v_id_1163_);
if (v_enableLog_1164_ == 0)
{
lean_dec_ref(v_env_1176_);
goto v___jp_1178_;
}
else
{
uint8_t v_isExporting_1181_; 
v_isExporting_1181_ = lean_ctor_get_uint8(v_env_1176_, sizeof(void*)*8);
lean_dec_ref(v_env_1176_);
if (v_isExporting_1181_ == 0)
{
goto v___jp_1178_;
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__31(v_res_1177_);
if (lean_obj_tag(v___x_1182_) == 1)
{
lean_object* v_val_1183_; lean_object* v_fst_1184_; lean_object* v___x_1185_; 
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_fst_1184_ = lean_ctor_get(v_val_1183_, 0);
lean_inc(v_fst_1184_);
lean_dec(v_val_1183_);
v___x_1185_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40(v_fst_1184_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
lean_dec(v_res_1177_);
v___x_1190_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_dec_ref_known(v_a_1186_, 1);
lean_del_object(v___x_1188_);
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_res_1177_);
v_a_1195_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1185_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1185_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_dec(v___x_1182_);
goto v___jp_1178_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_res_1177_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34___boxed(lean_object* v_id_1203_, lean_object* v_enableLog_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v_enableLog_boxed_1210_; lean_object* v_res_1211_; 
v_enableLog_boxed_1210_ = lean_unbox(v_enableLog_1204_);
v_res_1211_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v_id_1203_, v_enableLog_boxed_1210_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(lean_object* v_n_u2080_1216_, lean_object* v_filter_1217_, lean_object* v_view_x3f_1218_, lean_object* v_n_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1295_; 
if (lean_obj_tag(v_view_x3f_1218_) == 1)
{
lean_object* v_val_1322_; lean_object* v_imported_1323_; lean_object* v_ctx_1324_; lean_object* v_scopes_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
v_val_1322_ = lean_ctor_get(v_view_x3f_1218_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_view_x3f_1218_, 1);
v_imported_1323_ = lean_ctor_get(v_val_1322_, 1);
v_ctx_1324_ = lean_ctor_get(v_val_1322_, 2);
v_scopes_1325_ = lean_ctor_get(v_val_1322_, 3);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_val_1322_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_val_1322_, 0);
lean_dec(v_unused_1334_);
v___x_1327_ = v_val_1322_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_scopes_1325_);
lean_inc(v_ctx_1324_);
lean_inc(v_imported_1323_);
lean_dec(v_val_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_n_1219_);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_n_1219_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_imported_1323_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_ctx_1324_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_scopes_1325_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_MacroScopesView_review(v___x_1330_);
v___y_1295_ = v___x_1331_;
goto v___jp_1294_;
}
}
}
else
{
lean_dec(v_view_x3f_1218_);
v___y_1295_ = v_n_1219_;
goto v___jp_1294_;
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
v___jp_1228_:
{
lean_object* v___x_1231_; 
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1231_ = lean_apply_5(v___y_1230_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1251_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1251_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1251_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v___y_1229_);
v___x_1236_ = lean_box(0);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v_a_1232_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_a_1232_, 0);
lean_dec(v_unused_1250_);
v___x_1241_ = v_a_1232_;
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v_a_1232_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___y_1229_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___y_1229_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1244_);
v___x_1246_ = v___x_1234_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v___y_1229_);
v_a_1252_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1231_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1231_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
v___jp_1260_:
{
lean_object* v___x_1263_; 
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1263_ = lean_apply_5(v___y_1262_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1285_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1285_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1285_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec(v___y_1261_);
lean_dec_ref(v_filter_1217_);
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
lean_object* v___x_1272_; 
lean_dec_ref_known(v_a_1264_, 1);
lean_del_object(v___x_1266_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1261_);
v___x_1272_ = lean_apply_6(v_filter_1217_, v___y_1261_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; uint8_t v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___f_1275_; 
v___f_1275_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1229_ = v___y_1261_;
v___y_1230_ = v___f_1275_;
goto v___jp_1228_;
}
else
{
lean_object* v___f_1276_; 
v___f_1276_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1229_ = v___y_1261_;
v___y_1230_ = v___f_1276_;
goto v___jp_1228_;
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v___y_1261_);
v_a_1277_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1272_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1272_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v___y_1261_);
lean_dec_ref(v_filter_1217_);
v_a_1286_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1263_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1263_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
v___jp_1294_:
{
uint8_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = 0;
lean_inc(v___y_1295_);
v___x_1297_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34(v___y_1295_, v___x_1296_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1313_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1313_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1313_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
if (lean_obj_tag(v_a_1298_) == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec(v___y_1295_);
lean_dec_ref(v_filter_1217_);
v___x_1302_ = lean_box(0);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v_val_1306_; 
lean_del_object(v___x_1300_);
v_val_1306_ = lean_ctor_get(v_a_1298_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v_a_1298_, 1);
if (lean_obj_tag(v_val_1306_) == 1)
{
lean_object* v_head_1307_; lean_object* v_tail_1308_; 
v_head_1307_ = lean_ctor_get(v_val_1306_, 0);
lean_inc(v_head_1307_);
v_tail_1308_ = lean_ctor_get(v_val_1306_, 1);
lean_inc(v_tail_1308_);
lean_dec_ref_known(v_val_1306_, 2);
if (lean_obj_tag(v_tail_1308_) == 0)
{
lean_object* v_fst_1309_; uint8_t v___x_1310_; 
v_fst_1309_ = lean_ctor_get(v_head_1307_, 0);
lean_inc(v_fst_1309_);
lean_dec(v_head_1307_);
v___x_1310_ = lean_name_eq(v_fst_1309_, v_n_u2080_1216_);
lean_dec(v_fst_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___f_1311_; 
v___f_1311_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1261_ = v___y_1295_;
v___y_1262_ = v___f_1311_;
goto v___jp_1260_;
}
else
{
lean_object* v___f_1312_; 
v___f_1312_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1261_ = v___y_1295_;
v___y_1262_ = v___f_1312_;
goto v___jp_1260_;
}
}
else
{
lean_dec(v_tail_1308_);
lean_dec(v_head_1307_);
lean_dec(v___y_1295_);
lean_dec_ref(v_filter_1217_);
goto v___jp_1225_;
}
}
else
{
lean_dec(v_val_1306_);
lean_dec(v___y_1295_);
lean_dec_ref(v_filter_1217_);
goto v___jp_1225_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v___y_1295_);
lean_dec_ref(v_filter_1217_);
v_a_1314_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1297_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1297_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___boxed(lean_object* v_n_u2080_1335_, lean_object* v_filter_1336_, lean_object* v_view_x3f_1337_, lean_object* v_n_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1335_, v_filter_1336_, v_view_x3f_1337_, v_n_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v_n_u2080_1335_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(lean_object* v_n_u2080_1345_, lean_object* v_filter_1346_, lean_object* v_view_x3f_1347_, lean_object* v_as_x27_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
if (lean_obj_tag(v_as_x27_1348_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_view_x3f_1347_);
lean_dec_ref(v_filter_1346_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_b_1349_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v_head_1357_; lean_object* v_tail_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1397_; 
v_head_1357_ = lean_ctor_get(v_as_x27_1348_, 0);
v_tail_1358_ = lean_ctor_get(v_as_x27_1348_, 1);
v_snd_1359_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v_b_1349_, 0);
lean_dec(v_unused_1398_);
v___x_1361_ = v_b_1349_;
v_isShared_1362_ = v_isSharedCheck_1397_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_dec(v_b_1349_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1397_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l_Lean_Name_appendCore(v_head_1357_, v_snd_1359_);
lean_inc(v___x_1363_);
lean_inc(v_view_x3f_1347_);
lean_inc_ref(v_filter_1346_);
v___x_1364_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1345_, v_filter_1346_, v_view_x3f_1347_, v___x_1363_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1388_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1388_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1388_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
if (lean_obj_tag(v_a_1365_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_del_object(v___x_1367_);
v___x_1369_ = lean_box(0);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1363_);
lean_ctor_set(v___x_1361_, 0, v___x_1369_);
v___x_1371_ = v___x_1361_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1363_);
v___x_1371_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
v_as_x27_1348_ = v_tail_1358_;
v_b_1349_ = v___x_1371_;
goto _start;
}
}
else
{
lean_object* v___x_1375_; 
lean_dec(v_view_x3f_1347_);
lean_dec_ref(v_filter_1346_);
lean_inc_ref(v_a_1365_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1363_);
lean_ctor_set(v___x_1361_, 0, v_a_1365_);
v___x_1375_ = v___x_1361_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1365_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1363_);
v___x_1375_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1385_; 
v_isSharedCheck_1385_ = !lean_is_exclusive(v_a_1365_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v_a_1365_, 0);
lean_dec(v_unused_1386_);
v___x_1377_ = v_a_1365_;
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v_a_1365_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1375_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1380_);
v___x_1382_ = v___x_1367_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
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
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v___x_1363_);
lean_del_object(v___x_1361_);
lean_dec(v_view_x3f_1347_);
lean_dec_ref(v_filter_1346_);
v_a_1389_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1364_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1364_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg___boxed(lean_object* v_n_u2080_1399_, lean_object* v_filter_1400_, lean_object* v_view_x3f_1401_, lean_object* v_as_x27_1402_, lean_object* v_b_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1399_, v_filter_1400_, v_view_x3f_1401_, v_as_x27_1402_, v_b_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_as_x27_1402_);
lean_dec(v_n_u2080_1399_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(lean_object* v_n_u2080_1413_, lean_object* v_filter_1414_, lean_object* v_view_x3f_1415_, lean_object* v_n_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___y_1423_; uint8_t v___x_1464_; 
v___x_1464_ = l_Lean_Name_hasMacroScopes(v_n_1416_);
if (v___x_1464_ == 0)
{
lean_object* v___f_1465_; 
v___f_1465_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__1));
v___y_1423_ = v___f_1465_;
goto v___jp_1422_;
}
else
{
lean_object* v___f_1466_; 
v___f_1466_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25___closed__0));
v___y_1423_ = v___f_1466_;
goto v___jp_1422_;
}
v___jp_1422_:
{
lean_object* v___x_1424_; 
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1424_ = lean_apply_5(v___y_1423_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, lean_box(0));
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1455_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
if (lean_obj_tag(v_a_1425_) == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec(v_n_1416_);
lean_dec(v_view_x3f_1415_);
lean_dec_ref(v_filter_1414_);
v___x_1429_ = lean_box(0);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref_known(v_a_1425_, 1);
lean_del_object(v___x_1427_);
v___x_1433_ = l_Lean_privateToUserName(v_n_1416_);
v___x_1434_ = l_Lean_Name_componentsRev(v___x_1433_);
v___x_1435_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___closed__0));
v___x_1436_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_1413_, v_filter_1414_, v_view_x3f_1415_, v___x_1434_, v___x_1435_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___x_1434_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_val_1441_; lean_object* v_fst_1442_; lean_object* v___x_1444_; 
v_val_1441_ = lean_ctor_get(v_a_1437_, 0);
lean_inc(v_val_1441_);
lean_dec(v_a_1437_);
v_fst_1442_ = lean_ctor_get(v_val_1441_, 0);
lean_inc(v_fst_1442_);
lean_dec(v_val_1441_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_fst_1442_);
v___x_1444_ = v___x_1439_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1436_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1436_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_n_1416_);
lean_dec(v_view_x3f_1415_);
lean_dec_ref(v_filter_1414_);
v_a_1456_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1424_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1424_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22___boxed(lean_object* v_n_u2080_1467_, lean_object* v_filter_1468_, lean_object* v_view_x3f_1469_, lean_object* v_n_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1467_, v_filter_1468_, v_view_x3f_1469_, v_n_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_n_u2080_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(lean_object* v_n_u2080_1477_, lean_object* v_filter_1478_, lean_object* v_as_1479_, lean_object* v_i_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_array_get_size(v_as_1479_);
v___x_1487_ = lean_nat_dec_lt(v_i_1480_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec(v_i_1480_);
lean_dec_ref(v_filter_1478_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_array_fget_borrowed(v_as_1479_, v_i_1480_);
lean_inc(v___x_1491_);
lean_inc_ref(v_filter_1478_);
v___x_1492_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1477_, v_filter_1478_, v___x_1490_, v___x_1491_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
if (lean_obj_tag(v_a_1493_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_i_1480_, v___x_1494_);
lean_dec(v_i_1480_);
v_i_1480_ = v___x_1495_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_1493_, 1);
lean_dec(v_i_1480_);
lean_dec_ref(v_filter_1478_);
return v___x_1492_;
}
}
else
{
lean_dec(v_i_1480_);
lean_dec_ref(v_filter_1478_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23___boxed(lean_object* v_n_u2080_1497_, lean_object* v_filter_1498_, lean_object* v_as_1499_, lean_object* v_i_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1497_, v_filter_1498_, v_as_1499_, v_i_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec_ref(v_as_1499_);
lean_dec(v_n_u2080_1497_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(lean_object* v_n_u2081_1507_, lean_object* v_as_1508_, size_t v_i_1509_, size_t v_stop_1510_, lean_object* v_b_1511_){
_start:
{
lean_object* v___y_1513_; uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_eq(v_i_1509_, v_stop_1510_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1518_ = lean_array_uget_borrowed(v_as_1508_, v_i_1509_);
v___x_1519_ = l_Lean_Name_getPrefix(v___x_1518_);
v___x_1520_ = l_Lean_Name_getPrefix(v_n_u2081_1507_);
v___x_1521_ = l_Lean_Name_isPrefixOf(v___x_1519_, v___x_1520_);
lean_dec(v___x_1520_);
lean_dec(v___x_1519_);
if (v___x_1521_ == 0)
{
v___y_1513_ = v_b_1511_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1522_; 
lean_inc(v___x_1518_);
v___x_1522_ = lean_array_push(v_b_1511_, v___x_1518_);
v___y_1513_ = v___x_1522_;
goto v___jp_1512_;
}
}
else
{
return v_b_1511_;
}
v___jp_1512_:
{
size_t v___x_1514_; size_t v___x_1515_; 
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_add(v_i_1509_, v___x_1514_);
v_i_1509_ = v___x_1515_;
v_b_1511_ = v___y_1513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24___boxed(lean_object* v_n_u2081_1523_, lean_object* v_as_1524_, lean_object* v_i_1525_, lean_object* v_stop_1526_, lean_object* v_b_1527_){
_start:
{
size_t v_i_boxed_1528_; size_t v_stop_boxed_1529_; lean_object* v_res_1530_; 
v_i_boxed_1528_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_stop_boxed_1529_ = lean_unbox_usize(v_stop_1526_);
lean_dec(v_stop_1526_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1523_, v_as_1524_, v_i_boxed_1528_, v_stop_boxed_1529_, v_b_1527_);
lean_dec_ref(v_as_1524_);
lean_dec(v_n_u2081_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(lean_object* v_n_u2080_1533_, uint8_t v_fullNames_1534_, uint8_t v_allowHorizAliases_1535_, lean_object* v_filter_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_view_1542_; lean_object* v_name_1543_; lean_object* v_n_u2081_1544_; 
lean_inc(v_n_u2080_1533_);
v_view_1542_ = l_Lean_extractMacroScopes(v_n_u2080_1533_);
v_name_1543_ = lean_ctor_get(v_view_1542_, 0);
lean_inc(v_name_1543_);
v_n_u2081_1544_ = l_Lean_privateToUserName(v_name_1543_);
if (v_fullNames_1534_ == 0)
{
lean_object* v___x_1545_; lean_object* v_aliases_1547_; lean_object* v_env_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1545_ = lean_st_ref_get(v___y_1540_);
v_env_1562_ = lean_ctor_get(v___x_1545_, 0);
lean_inc_ref(v_env_1562_);
lean_dec(v___x_1545_);
lean_inc(v_n_u2080_1533_);
v___x_1563_ = l_Lean_getRevAliases(v_env_1562_, v_n_u2080_1533_);
v___x_1564_ = lean_array_mk(v___x_1563_);
if (v_allowHorizAliases_1535_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_array_get_size(v___x_1564_);
v___x_1567_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___closed__0));
v___x_1568_ = lean_nat_dec_lt(v___x_1565_, v___x_1566_);
if (v___x_1568_ == 0)
{
lean_dec_ref(v___x_1564_);
v_aliases_1547_ = v___x_1567_;
goto v___jp_1546_;
}
else
{
size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = lean_usize_of_nat(v___x_1566_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__24(v_n_u2081_1544_, v___x_1564_, v___x_1569_, v___x_1570_, v___x_1567_);
lean_dec_ref(v___x_1564_);
v_aliases_1547_ = v___x_1571_;
goto v___jp_1546_;
}
}
else
{
v_aliases_1547_ = v___x_1564_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_1536_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__23(v_n_u2080_1533_, v_filter_1536_, v_aliases_1547_, v___x_1548_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v_aliases_1547_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
if (lean_obj_tag(v_a_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1560_; 
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1561_);
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 1);
lean_ctor_set(v___x_1552_, 0, v_view_1542_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_view_1542_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = l_Lean_rootNamespace;
v___x_1557_ = l_Lean_Name_append(v___x_1556_, v_n_u2081_1544_);
v___x_1558_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22(v_n_u2080_1533_, v_filter_1536_, v___x_1555_, v___x_1557_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v_n_u2080_1533_);
return v___x_1558_;
}
}
}
else
{
lean_dec_ref_known(v_a_1550_, 1);
lean_dec(v_n_u2081_1544_);
lean_dec_ref(v_view_1542_);
lean_dec_ref(v_filter_1536_);
lean_dec(v_n_u2080_1533_);
return v___x_1549_;
}
}
else
{
lean_dec(v_n_u2081_1544_);
lean_dec_ref(v_view_1542_);
lean_dec_ref(v_filter_1536_);
lean_dec(v_n_u2080_1533_);
return v___x_1549_;
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_view_1542_);
lean_inc(v_n_u2081_1544_);
lean_inc_ref(v___x_1572_);
lean_inc_ref(v_filter_1536_);
v___x_1573_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1533_, v_filter_1536_, v___x_1572_, v_n_u2081_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
if (lean_obj_tag(v_a_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = l_Lean_rootNamespace;
v___x_1576_ = l_Lean_Name_append(v___x_1575_, v_n_u2081_1544_);
v___x_1577_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25(v_n_u2080_1533_, v_filter_1536_, v___x_1572_, v___x_1576_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v_n_u2080_1533_);
return v___x_1577_;
}
else
{
lean_dec_ref_known(v_a_1574_, 1);
lean_dec_ref_known(v___x_1572_, 1);
lean_dec(v_n_u2081_1544_);
lean_dec_ref(v_filter_1536_);
lean_dec(v_n_u2080_1533_);
return v___x_1573_;
}
}
else
{
lean_dec_ref_known(v___x_1572_, 1);
lean_dec(v_n_u2081_1544_);
lean_dec_ref(v_filter_1536_);
lean_dec(v_n_u2080_1533_);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12___boxed(lean_object* v_n_u2080_1578_, lean_object* v_fullNames_1579_, lean_object* v_allowHorizAliases_1580_, lean_object* v_filter_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_fullNames_boxed_1587_; uint8_t v_allowHorizAliases_boxed_1588_; lean_object* v_res_1589_; 
v_fullNames_boxed_1587_ = lean_unbox(v_fullNames_1579_);
v_allowHorizAliases_boxed_1588_ = lean_unbox(v_allowHorizAliases_1580_);
v_res_1589_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1578_, v_fullNames_boxed_1587_, v_allowHorizAliases_boxed_1588_, v_filter_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(lean_object* v_n_u2080_1593_, uint8_t v_fullNames_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; 
v___x_1600_ = 0;
v___f_1601_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___closed__0));
v___x_1602_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12(v_n_u2080_1593_, v_fullNames_1594_, v___x_1600_, v___f_1601_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5___boxed(lean_object* v_n_u2080_1603_, lean_object* v_fullNames_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_fullNames_boxed_1610_; lean_object* v_res_1611_; 
v_fullNames_boxed_1610_ = lean_unbox(v_fullNames_1604_);
v_res_1611_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_n_u2080_1603_, v_fullNames_boxed_1610_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
lean_ctor_set(v___x_1617_, 3, v___x_1616_);
lean_ctor_set(v___x_1617_, 4, v___x_1615_);
lean_ctor_set(v___x_1617_, 5, v___x_1615_);
lean_ctor_set(v___x_1617_, 6, v___x_1615_);
lean_ctor_set(v___x_1617_, 7, v___x_1615_);
lean_ctor_set(v___x_1617_, 8, v___x_1615_);
lean_ctor_set(v___x_1617_, 9, v___x_1615_);
lean_ctor_set(v___x_1617_, 10, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(32u);
v___x_1619_ = lean_mk_empty_array_with_capacity(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1621_ = ((size_t)5ULL);
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = lean_unsigned_to_nat(32u);
v___x_1624_ = lean_mk_empty_array_with_capacity(v___x_1623_);
v___x_1625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_1626_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v___x_1624_);
lean_ctor_set(v___x_1626_, 2, v___x_1622_);
lean_ctor_set(v___x_1626_, 3, v___x_1622_);
lean_ctor_set_usize(v___x_1626_, 4, v___x_1621_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1627_ = lean_box(1);
v___x_1628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
lean_ctor_set(v___x_1630_, 2, v___x_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; lean_object* v_env_1636_; lean_object* v_options_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1635_ = lean_st_ref_get(v___y_1633_);
v_env_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_ref(v_env_1636_);
lean_dec(v___x_1635_);
v_options_1637_ = lean_ctor_get(v___y_1632_, 2);
v___x_1638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_1639_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1637_);
v___x_1640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1640_, 0, v_env_1636_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
lean_ctor_set(v___x_1640_, 3, v_options_1637_);
v___x_1641_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_msgData_1631_);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_ref_1648_, lean_object* v_msgData_1649_, uint8_t v_severity_1650_, uint8_t v_isSilent_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1692_; lean_object* v___y_1693_; uint8_t v___y_1694_; lean_object* v___y_1695_; uint8_t v___y_1696_; lean_object* v___y_1697_; uint8_t v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; uint8_t v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1728_; lean_object* v___y_1729_; uint8_t v___y_1730_; lean_object* v___y_1731_; uint8_t v___y_1732_; lean_object* v___y_1733_; uint8_t v___y_1734_; uint8_t v___x_1739_; lean_object* v___y_1741_; lean_object* v___y_1742_; uint8_t v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; uint8_t v___y_1746_; uint8_t v___y_1747_; uint8_t v___y_1749_; uint8_t v___x_1764_; 
v___x_1739_ = 2;
v___x_1764_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1650_, v___x_1739_);
if (v___x_1764_ == 0)
{
v___y_1749_ = v___x_1764_;
goto v___jp_1748_;
}
else
{
uint8_t v___x_1765_; 
lean_inc_ref(v_msgData_1649_);
v___x_1765_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1649_);
v___y_1749_ = v___x_1765_;
goto v___jp_1748_;
}
v___jp_1655_:
{
lean_object* v___x_1665_; lean_object* v_currNamespace_1666_; lean_object* v_openDecls_1667_; lean_object* v_env_1668_; lean_object* v_nextMacroScope_1669_; lean_object* v_ngen_1670_; lean_object* v_auxDeclNGen_1671_; lean_object* v_traceState_1672_; lean_object* v_cache_1673_; lean_object* v_messages_1674_; lean_object* v_infoState_1675_; lean_object* v_snapshotTasks_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1690_; 
v___x_1665_ = lean_st_ref_take(v___y_1664_);
v_currNamespace_1666_ = lean_ctor_get(v___y_1663_, 6);
v_openDecls_1667_ = lean_ctor_get(v___y_1663_, 7);
v_env_1668_ = lean_ctor_get(v___x_1665_, 0);
v_nextMacroScope_1669_ = lean_ctor_get(v___x_1665_, 1);
v_ngen_1670_ = lean_ctor_get(v___x_1665_, 2);
v_auxDeclNGen_1671_ = lean_ctor_get(v___x_1665_, 3);
v_traceState_1672_ = lean_ctor_get(v___x_1665_, 4);
v_cache_1673_ = lean_ctor_get(v___x_1665_, 5);
v_messages_1674_ = lean_ctor_get(v___x_1665_, 6);
v_infoState_1675_ = lean_ctor_get(v___x_1665_, 7);
v_snapshotTasks_1676_ = lean_ctor_get(v___x_1665_, 8);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1678_ = v___x_1665_;
v_isShared_1679_ = v_isSharedCheck_1690_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_snapshotTasks_1676_);
lean_inc(v_infoState_1675_);
lean_inc(v_messages_1674_);
lean_inc(v_cache_1673_);
lean_inc(v_traceState_1672_);
lean_inc(v_auxDeclNGen_1671_);
lean_inc(v_ngen_1670_);
lean_inc(v_nextMacroScope_1669_);
lean_inc(v_env_1668_);
lean_dec(v___x_1665_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1690_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_inc(v_openDecls_1667_);
lean_inc(v_currNamespace_1666_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_currNamespace_1666_);
lean_ctor_set(v___x_1680_, 1, v_openDecls_1667_);
v___x_1681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___y_1659_);
lean_inc_ref(v___y_1662_);
lean_inc_ref(v___y_1656_);
v___x_1682_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1682_, 0, v___y_1656_);
lean_ctor_set(v___x_1682_, 1, v___y_1658_);
lean_ctor_set(v___x_1682_, 2, v___y_1661_);
lean_ctor_set(v___x_1682_, 3, v___y_1662_);
lean_ctor_set(v___x_1682_, 4, v___x_1681_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5, v___y_1657_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5 + 1, v___y_1660_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*5 + 2, v_isSilent_1651_);
v___x_1683_ = l_Lean_MessageLog_add(v___x_1682_, v_messages_1674_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 6, v___x_1683_);
v___x_1685_ = v___x_1678_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_env_1668_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_nextMacroScope_1669_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_ngen_1670_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_auxDeclNGen_1671_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_traceState_1672_);
lean_ctor_set(v_reuseFailAlloc_1689_, 5, v_cache_1673_);
lean_ctor_set(v_reuseFailAlloc_1689_, 6, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 7, v_infoState_1675_);
lean_ctor_set(v_reuseFailAlloc_1689_, 8, v_snapshotTasks_1676_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_st_ref_put(v___y_1664_, v___x_1685_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
v___jp_1691_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1715_; 
v___x_1700_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1649_);
v___x_1701_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v___x_1700_, v___y_1652_, v___y_1653_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_inc_ref_n(v___y_1693_, 2);
v___x_1706_ = l_Lean_FileMap_toPosition(v___y_1693_, v___y_1697_);
lean_dec(v___y_1697_);
v___x_1707_ = l_Lean_FileMap_toPosition(v___y_1693_, v___y_1699_);
lean_dec(v___y_1699_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
if (v___y_1694_ == 0)
{
lean_del_object(v___x_1704_);
lean_dec_ref(v___y_1692_);
v___y_1656_ = v___y_1695_;
v___y_1657_ = v___y_1696_;
v___y_1658_ = v___x_1706_;
v___y_1659_ = v_a_1702_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___x_1708_;
v___y_1662_ = v___x_1709_;
v___y_1663_ = v___y_1652_;
v___y_1664_ = v___y_1653_;
goto v___jp_1655_;
}
else
{
uint8_t v___x_1710_; 
lean_inc(v_a_1702_);
v___x_1710_ = l_Lean_MessageData_hasTag(v___y_1692_, v_a_1702_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1708_, 1);
lean_dec_ref(v___x_1706_);
lean_dec(v_a_1702_);
v___x_1711_ = lean_box(0);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1711_);
v___x_1713_ = v___x_1704_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_del_object(v___x_1704_);
v___y_1656_ = v___y_1695_;
v___y_1657_ = v___y_1696_;
v___y_1658_ = v___x_1706_;
v___y_1659_ = v_a_1702_;
v___y_1660_ = v___y_1698_;
v___y_1661_ = v___x_1708_;
v___y_1662_ = v___x_1709_;
v___y_1663_ = v___y_1652_;
v___y_1664_ = v___y_1653_;
goto v___jp_1655_;
}
}
}
}
v___jp_1716_:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Syntax_getTailPos_x3f(v___y_1720_, v___y_1722_);
lean_dec(v___y_1720_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_inc(v___y_1724_);
v___y_1692_ = v___y_1717_;
v___y_1693_ = v___y_1718_;
v___y_1694_ = v___y_1719_;
v___y_1695_ = v___y_1721_;
v___y_1696_ = v___y_1722_;
v___y_1697_ = v___y_1724_;
v___y_1698_ = v___y_1723_;
v___y_1699_ = v___y_1724_;
goto v___jp_1691_;
}
else
{
lean_object* v_val_1726_; 
v_val_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___y_1692_ = v___y_1717_;
v___y_1693_ = v___y_1718_;
v___y_1694_ = v___y_1719_;
v___y_1695_ = v___y_1721_;
v___y_1696_ = v___y_1722_;
v___y_1697_ = v___y_1724_;
v___y_1698_ = v___y_1723_;
v___y_1699_ = v_val_1726_;
goto v___jp_1691_;
}
}
v___jp_1727_:
{
lean_object* v_ref_1735_; lean_object* v___x_1736_; 
v_ref_1735_ = l_Lean_replaceRef(v_ref_1648_, v___y_1733_);
v___x_1736_ = l_Lean_Syntax_getPos_x3f(v_ref_1735_, v___y_1732_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___y_1717_ = v___y_1728_;
v___y_1718_ = v___y_1729_;
v___y_1719_ = v___y_1730_;
v___y_1720_ = v_ref_1735_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1734_;
v___y_1724_ = v___x_1737_;
goto v___jp_1716_;
}
else
{
lean_object* v_val_1738_; 
v_val_1738_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v___x_1736_, 1);
v___y_1717_ = v___y_1728_;
v___y_1718_ = v___y_1729_;
v___y_1719_ = v___y_1730_;
v___y_1720_ = v_ref_1735_;
v___y_1721_ = v___y_1731_;
v___y_1722_ = v___y_1732_;
v___y_1723_ = v___y_1734_;
v___y_1724_ = v_val_1738_;
goto v___jp_1716_;
}
}
v___jp_1740_:
{
if (v___y_1747_ == 0)
{
v___y_1728_ = v___y_1742_;
v___y_1729_ = v___y_1741_;
v___y_1730_ = v___y_1743_;
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1746_;
v___y_1733_ = v___y_1745_;
v___y_1734_ = v_severity_1650_;
goto v___jp_1727_;
}
else
{
v___y_1728_ = v___y_1742_;
v___y_1729_ = v___y_1741_;
v___y_1730_ = v___y_1743_;
v___y_1731_ = v___y_1744_;
v___y_1732_ = v___y_1746_;
v___y_1733_ = v___y_1745_;
v___y_1734_ = v___x_1739_;
goto v___jp_1727_;
}
}
v___jp_1748_:
{
if (v___y_1749_ == 0)
{
lean_object* v_fileName_1750_; lean_object* v_fileMap_1751_; lean_object* v_options_1752_; lean_object* v_ref_1753_; uint8_t v_suppressElabErrors_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; 
v_fileName_1750_ = lean_ctor_get(v___y_1652_, 0);
v_fileMap_1751_ = lean_ctor_get(v___y_1652_, 1);
v_options_1752_ = lean_ctor_get(v___y_1652_, 2);
v_ref_1753_ = lean_ctor_get(v___y_1652_, 5);
v_suppressElabErrors_1754_ = lean_ctor_get_uint8(v___y_1652_, sizeof(void*)*14 + 1);
v___x_1755_ = lean_box(v_suppressElabErrors_1754_);
v___x_1756_ = lean_box(v___y_1749_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1757_, 0, v___x_1755_);
lean_closure_set(v___f_1757_, 1, v___x_1756_);
v___x_1758_ = 1;
v___x_1759_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1650_, v___x_1758_);
if (v___x_1759_ == 0)
{
v___y_1741_ = v_fileMap_1751_;
v___y_1742_ = v___f_1757_;
v___y_1743_ = v_suppressElabErrors_1754_;
v___y_1744_ = v_fileName_1750_;
v___y_1745_ = v_ref_1753_;
v___y_1746_ = v___y_1749_;
v___y_1747_ = v___x_1759_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = l_Lean_warningAsError;
v___x_1761_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_1752_, v___x_1760_);
v___y_1741_ = v_fileMap_1751_;
v___y_1742_ = v___f_1757_;
v___y_1743_ = v_suppressElabErrors_1754_;
v___y_1744_ = v_fileName_1750_;
v___y_1745_ = v_ref_1753_;
v___y_1746_ = v___y_1749_;
v___y_1747_ = v___x_1761_;
goto v___jp_1740_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v_msgData_1649_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1766_, lean_object* v_msgData_1767_, lean_object* v_severity_1768_, lean_object* v_isSilent_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_severity_boxed_1773_; uint8_t v_isSilent_boxed_1774_; lean_object* v_res_1775_; 
v_severity_boxed_1773_ = lean_unbox(v_severity_1768_);
v_isSilent_boxed_1774_ = lean_unbox(v_isSilent_1769_);
v_res_1775_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1766_, v_msgData_1767_, v_severity_boxed_1773_, v_isSilent_boxed_1774_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_ref_1766_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_1776_, uint8_t v_severity_1777_, uint8_t v_isSilent_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_ref_1782_; lean_object* v___x_1783_; 
v_ref_1782_ = lean_ctor_get(v___y_1779_, 5);
v___x_1783_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_ref_1782_, v_msgData_1776_, v_severity_1777_, v_isSilent_1778_, v___y_1779_, v___y_1780_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_1784_, lean_object* v_severity_1785_, lean_object* v_isSilent_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_severity_boxed_1790_; uint8_t v_isSilent_boxed_1791_; lean_object* v_res_1792_; 
v_severity_boxed_1790_ = lean_unbox(v_severity_1785_);
v_isSilent_boxed_1791_ = lean_unbox(v_isSilent_1786_);
v_res_1792_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1784_, v_severity_boxed_1790_, v_isSilent_boxed_1791_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(lean_object* v_msgData_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = 1;
v___x_1798_ = 0;
v___x_1799_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1_spec__2(v_msgData_1793_, v___x_1797_, v___x_1798_, v___y_1794_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msgData_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v_env_1809_; lean_object* v___x_1810_; lean_object* v_toEnvExtension_1811_; lean_object* v_asyncMode_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_merged_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
v___x_1808_ = lean_st_ref_get(v___y_1806_);
v_env_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_env_1809_);
lean_dec(v___x_1808_);
v___x_1810_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1811_ = lean_ctor_get(v___x_1810_, 0);
v_asyncMode_1812_ = lean_ctor_get(v_toEnvExtension_1811_, 2);
v___x_1813_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1814_ = lean_box(0);
v___x_1815_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1813_, v___x_1810_, v_env_1809_, v_asyncMode_1812_, v___x_1814_);
v_merged_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1815_, 1);
lean_dec(v_unused_1825_);
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_merged_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v_merged_1816_);
lean_ctor_set(v___x_1818_, 0, v_o_1805_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_o_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_merged_1816_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1826_, v___y_1827_);
lean_dec(v___y_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_options_1833_; lean_object* v___x_1834_; 
v_options_1833_ = lean_ctor_get(v___y_1830_, 2);
lean_inc_ref(v_options_1833_);
v___x_1834_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_options_1833_, v___y_1831_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_ref_1843_; lean_object* v___x_1844_; lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1853_; 
v_ref_1843_ = lean_ctor_get(v___y_1840_, 5);
v___x_1844_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1839_, v___y_1840_, v___y_1841_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_inc(v_ref_1843_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_ref_1843_);
lean_ctor_set(v___x_1849_, 1, v_a_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 1);
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(lean_object* v_keys_1859_, lean_object* v_i_1860_, lean_object* v_k_1861_){
_start:
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_array_get_size(v_keys_1859_);
v___x_1863_ = lean_nat_dec_lt(v_i_1860_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec(v_i_1860_);
return v___x_1863_;
}
else
{
lean_object* v_k_x27_1864_; uint8_t v___x_1865_; 
v_k_x27_1864_ = lean_array_fget_borrowed(v_keys_1859_, v_i_1860_);
v___x_1865_ = l_Lean_instBEqExtraModUse_beq(v_k_1861_, v_k_x27_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_i_1860_, v___x_1866_);
lean_dec(v_i_1860_);
v_i_1860_ = v___x_1867_;
goto _start;
}
else
{
lean_dec(v_i_1860_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg___boxed(lean_object* v_keys_1869_, lean_object* v_i_1870_, lean_object* v_k_1871_){
_start:
{
uint8_t v_res_1872_; lean_object* v_r_1873_; 
v_res_1872_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_1869_, v_i_1870_, v_k_1871_);
lean_dec_ref(v_k_1871_);
lean_dec_ref(v_keys_1869_);
v_r_1873_ = lean_box(v_res_1872_);
return v_r_1873_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_x_1874_, size_t v_x_1875_, lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_es_1877_; lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v_j_1881_; lean_object* v___x_1882_; 
v_es_1877_ = lean_ctor_get(v_x_1874_, 0);
v___x_1878_ = lean_box(2);
v___x_1879_ = ((size_t)31ULL);
v___x_1880_ = lean_usize_land(v_x_1875_, v___x_1879_);
v_j_1881_ = lean_usize_to_nat(v___x_1880_);
v___x_1882_ = lean_array_get_borrowed(v___x_1878_, v_es_1877_, v_j_1881_);
lean_dec(v_j_1881_);
switch(lean_obj_tag(v___x_1882_))
{
case 0:
{
lean_object* v_key_1883_; uint8_t v___x_1884_; 
v_key_1883_ = lean_ctor_get(v___x_1882_, 0);
v___x_1884_ = l_Lean_instBEqExtraModUse_beq(v_x_1876_, v_key_1883_);
return v___x_1884_;
}
case 1:
{
lean_object* v_node_1885_; size_t v___x_1886_; size_t v___x_1887_; 
v_node_1885_ = lean_ctor_get(v___x_1882_, 0);
v___x_1886_ = ((size_t)5ULL);
v___x_1887_ = lean_usize_shift_right(v_x_1875_, v___x_1886_);
v_x_1874_ = v_node_1885_;
v_x_1875_ = v___x_1887_;
goto _start;
}
default: 
{
uint8_t v___x_1889_; 
v___x_1889_ = 0;
return v___x_1889_;
}
}
}
else
{
lean_object* v_ks_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_ks_1890_ = lean_ctor_get(v_x_1874_, 0);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_ks_1890_, v___x_1891_, v_x_1876_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
size_t v_x_45236__boxed_1896_; uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_x_45236__boxed_1896_ = lean_unbox_usize(v_x_1894_);
lean_dec(v_x_1894_);
v_res_1897_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1893_, v_x_45236__boxed_1896_, v_x_1895_);
lean_dec_ref(v_x_1895_);
lean_dec_ref(v_x_1893_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
uint64_t v___x_1901_; size_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1901_ = l_Lean_instHashableExtraModUse_hash(v_x_1900_);
v___x_1902_ = lean_uint64_to_usize(v___x_1901_);
v___x_1903_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_1899_, v___x_1902_, v_x_1900_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
uint8_t v_res_1906_; lean_object* v_r_1907_; 
v_res_1906_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_1904_, v_x_1905_);
lean_dec_ref(v_x_1905_);
lean_dec_ref(v_x_1904_);
v_r_1907_ = lean_box(v_res_1906_);
return v_r_1907_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1908_; double v___x_1909_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_float_of_nat(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(lean_object* v_cls_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_ref_1917_; lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1963_; 
v_ref_1917_ = lean_ctor_get(v___y_1914_, 5);
v___x_1918_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0(v_msg_1913_, v___y_1914_, v___y_1915_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1963_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1963_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v_traceState_1924_; lean_object* v_env_1925_; lean_object* v_nextMacroScope_1926_; lean_object* v_ngen_1927_; lean_object* v_auxDeclNGen_1928_; lean_object* v_cache_1929_; lean_object* v_messages_1930_; lean_object* v_infoState_1931_; lean_object* v_snapshotTasks_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1962_; 
v___x_1923_ = lean_st_ref_take(v___y_1915_);
v_traceState_1924_ = lean_ctor_get(v___x_1923_, 4);
v_env_1925_ = lean_ctor_get(v___x_1923_, 0);
v_nextMacroScope_1926_ = lean_ctor_get(v___x_1923_, 1);
v_ngen_1927_ = lean_ctor_get(v___x_1923_, 2);
v_auxDeclNGen_1928_ = lean_ctor_get(v___x_1923_, 3);
v_cache_1929_ = lean_ctor_get(v___x_1923_, 5);
v_messages_1930_ = lean_ctor_get(v___x_1923_, 6);
v_infoState_1931_ = lean_ctor_get(v___x_1923_, 7);
v_snapshotTasks_1932_ = lean_ctor_get(v___x_1923_, 8);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1934_ = v___x_1923_;
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snapshotTasks_1932_);
lean_inc(v_infoState_1931_);
lean_inc(v_messages_1930_);
lean_inc(v_cache_1929_);
lean_inc(v_traceState_1924_);
lean_inc(v_auxDeclNGen_1928_);
lean_inc(v_ngen_1927_);
lean_inc(v_nextMacroScope_1926_);
lean_inc(v_env_1925_);
lean_dec(v___x_1923_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint64_t v_tid_1936_; lean_object* v_traces_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1961_; 
v_tid_1936_ = lean_ctor_get_uint64(v_traceState_1924_, sizeof(void*)*1);
v_traces_1937_ = lean_ctor_get(v_traceState_1924_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_traceState_1924_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1939_ = v_traceState_1924_;
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_traces_1937_);
lean_dec(v_traceState_1924_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; double v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__0);
v___x_1943_ = 0;
v___x_1944_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1945_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1945_, 0, v_cls_1912_);
lean_ctor_set(v___x_1945_, 1, v___x_1941_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3, v___x_1942_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3 + 8, v___x_1942_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*3 + 16, v___x_1943_);
v___x_1946_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___closed__1));
v___x_1947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v_a_1919_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
lean_inc(v_ref_1917_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_ref_1917_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_PersistentArray_push___redArg(v_traces_1937_, v___x_1948_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1949_);
v___x_1951_ = v___x_1939_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1949_);
lean_ctor_set_uint64(v_reuseFailAlloc_1960_, sizeof(void*)*1, v_tid_1936_);
v___x_1951_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v___x_1951_);
v___x_1953_ = v___x_1934_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_env_1925_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_nextMacroScope_1926_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_ngen_1927_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_auxDeclNGen_1928_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 5, v_cache_1929_);
lean_ctor_set(v_reuseFailAlloc_1959_, 6, v_messages_1930_);
lean_ctor_set(v_reuseFailAlloc_1959_, 7, v_infoState_1931_);
lean_ctor_set(v_reuseFailAlloc_1959_, 8, v_snapshotTasks_1932_);
v___x_1953_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = lean_st_ref_put(v___y_1915_, v___x_1953_);
v___x_1955_ = lean_box(0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1955_);
v___x_1957_ = v___x_1921_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9___boxed(lean_object* v_cls_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_1964_, v_msg_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1969_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_1973_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_1974_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1975_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__38_spec__42_spec__44___closed__0));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_cls_1993_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_1994_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_1995_ = l_Lean_Name_append(v___x_1994_, v_cls_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_2006_, uint8_t v_isMeta_2007_, lean_object* v_hint_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v_env_2013_; uint8_t v_isExporting_2014_; lean_object* v___x_2015_; lean_object* v_env_2016_; lean_object* v___x_2017_; lean_object* v_entry_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___y_2023_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2012_ = lean_st_ref_get(v___y_2010_);
v_env_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_ref(v_env_2013_);
lean_dec(v___x_2012_);
v_isExporting_2014_ = lean_ctor_get_uint8(v_env_2013_, sizeof(void*)*8);
lean_dec_ref(v_env_2013_);
v___x_2015_ = lean_st_ref_get(v___y_2010_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2015_);
v___x_2017_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_2006_);
v_entry_2018_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2018_, 0, v_mod_2006_);
lean_ctor_set_uint8(v_entry_2018_, sizeof(void*)*1, v_isExporting_2014_);
lean_ctor_set_uint8(v_entry_2018_, sizeof(void*)*1 + 1, v_isMeta_2007_);
v___x_2019_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2020_ = lean_box(1);
v___x_2021_ = lean_box(0);
v___x_2048_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2017_, v___x_2019_, v_env_2016_, v___x_2020_, v___x_2021_);
v___x_2049_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v___x_2048_, v_entry_2018_);
lean_dec(v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v_options_2050_; uint8_t v_hasTrace_2051_; 
v_options_2050_ = lean_ctor_get(v___y_2009_, 2);
v_hasTrace_2051_ = lean_ctor_get_uint8(v_options_2050_, sizeof(void*)*1);
if (v_hasTrace_2051_ == 0)
{
lean_dec(v_hint_2008_);
lean_dec(v_mod_2006_);
v___y_2023_ = v___y_2010_;
goto v___jp_2022_;
}
else
{
lean_object* v_inheritedTraceOptions_2052_; lean_object* v_cls_2053_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_inheritedTraceOptions_2052_ = lean_ctor_get(v___y_2009_, 13);
v_cls_2053_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_2073_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_2074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2052_, v_options_2050_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_hint_2008_);
lean_dec(v_mod_2006_);
v___y_2023_ = v___y_2010_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2075_; lean_object* v___y_2077_; 
v___x_2075_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__16);
if (v_isExporting_2014_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_2077_ = v___x_2084_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__22));
v___y_2077_ = v___x_2085_;
goto v___jp_2076_;
}
v___jp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_inc_ref(v___y_2077_);
v___x_2078_ = l_Lean_stringToMessageData(v___y_2077_);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2075_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__18);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
if (v_isMeta_2007_ == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_2060_ = v___x_2081_;
v___y_2061_ = v___x_2082_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2083_; 
v___x_2083_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__20));
v___y_2060_ = v___x_2081_;
v___y_2061_ = v___x_2083_;
goto v___jp_2059_;
}
}
}
v___jp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___y_2055_);
lean_ctor_set(v___x_2057_, 1, v___y_2056_);
v___x_2058_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__9(v_cls_2053_, v___x_2057_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_dec_ref_known(v___x_2058_, 1);
v___y_2023_ = v___y_2010_;
goto v___jp_2022_;
}
else
{
lean_dec_ref_known(v_entry_2018_, 1);
return v___x_2058_;
}
}
v___jp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
lean_inc_ref(v___y_2061_);
v___x_2062_ = l_Lean_stringToMessageData(v___y_2061_);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___y_2060_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_MessageData_ofName(v_mod_2006_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_Name_isAnonymous(v_hint_2008_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_2070_ = l_Lean_MessageData_ofName(v_hint_2008_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___y_2055_ = v___x_2067_;
v___y_2056_ = v___x_2071_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2072_; 
lean_dec(v_hint_2008_);
v___x_2072_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___y_2055_ = v___x_2067_;
v___y_2056_ = v___x_2072_;
goto v___jp_2054_;
}
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref_known(v_entry_2018_, 1);
lean_dec(v_hint_2008_);
lean_dec(v_mod_2006_);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v_toEnvExtension_2025_; lean_object* v_env_2026_; lean_object* v_nextMacroScope_2027_; lean_object* v_ngen_2028_; lean_object* v_auxDeclNGen_2029_; lean_object* v_traceState_2030_; lean_object* v_messages_2031_; lean_object* v_infoState_2032_; lean_object* v_snapshotTasks_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2046_; 
v___x_2024_ = lean_st_ref_take(v___y_2023_);
v_toEnvExtension_2025_ = lean_ctor_get(v___x_2019_, 0);
v_env_2026_ = lean_ctor_get(v___x_2024_, 0);
v_nextMacroScope_2027_ = lean_ctor_get(v___x_2024_, 1);
v_ngen_2028_ = lean_ctor_get(v___x_2024_, 2);
v_auxDeclNGen_2029_ = lean_ctor_get(v___x_2024_, 3);
v_traceState_2030_ = lean_ctor_get(v___x_2024_, 4);
v_messages_2031_ = lean_ctor_get(v___x_2024_, 6);
v_infoState_2032_ = lean_ctor_get(v___x_2024_, 7);
v_snapshotTasks_2033_ = lean_ctor_get(v___x_2024_, 8);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2024_, 5);
lean_dec(v_unused_2047_);
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_snapshotTasks_2033_);
lean_inc(v_infoState_2032_);
lean_inc(v_messages_2031_);
lean_inc(v_traceState_2030_);
lean_inc(v_auxDeclNGen_2029_);
lean_inc(v_ngen_2028_);
lean_inc(v_nextMacroScope_2027_);
lean_inc(v_env_2026_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2046_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_asyncMode_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v_asyncMode_2037_ = lean_ctor_get(v_toEnvExtension_2025_, 2);
v___x_2038_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2019_, v_env_2026_, v_entry_2018_, v_asyncMode_2037_, v___x_2021_);
v___x_2039_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__5);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 5, v___x_2039_);
lean_ctor_set(v___x_2035_, 0, v___x_2038_);
v___x_2041_ = v___x_2035_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_nextMacroScope_2027_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_ngen_2028_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_auxDeclNGen_2029_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_traceState_2030_);
lean_ctor_set(v_reuseFailAlloc_2045_, 5, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2045_, 6, v_messages_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 7, v_infoState_2032_);
lean_ctor_set(v_reuseFailAlloc_2045_, 8, v_snapshotTasks_2033_);
v___x_2041_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = lean_st_ref_put(v___y_2023_, v___x_2041_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_2088_, lean_object* v_isMeta_2089_, lean_object* v_hint_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v_isMeta_boxed_2094_; lean_object* v_res_2095_; 
v_isMeta_boxed_2094_ = lean_unbox(v_isMeta_2089_);
v_res_2095_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_mod_2088_, v_isMeta_boxed_2094_, v_hint_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_2096_, lean_object* v_declName_2097_, lean_object* v_as_2098_, size_t v_sz_2099_, size_t v_i_2100_, lean_object* v_b_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec(v_declName_2097_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_b_2101_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v_modules_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v_toImport_2112_; lean_object* v_module_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2107_ = l_Lean_Environment_header(v___x_2096_);
v_modules_2108_ = lean_ctor_get(v___x_2107_, 3);
lean_inc_ref(v_modules_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2110_ = lean_array_uget_borrowed(v_as_2098_, v_i_2100_);
v___x_2111_ = lean_array_get(v___x_2109_, v_modules_2108_, v_a_2110_);
lean_dec_ref(v_modules_2108_);
v_toImport_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_toImport_2112_);
lean_dec(v___x_2111_);
v_module_2113_ = lean_ctor_get(v_toImport_2112_, 0);
lean_inc(v_module_2113_);
lean_dec_ref(v_toImport_2112_);
v___x_2114_ = 0;
lean_inc(v_declName_2097_);
v___x_2115_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2113_, v___x_2114_, v_declName_2097_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; 
lean_dec_ref_known(v___x_2115_, 1);
v___x_2116_ = lean_box(0);
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_add(v_i_2100_, v___x_2117_);
v_i_2100_ = v___x_2118_;
v_b_2101_ = v___x_2116_;
goto _start;
}
else
{
lean_dec(v_declName_2097_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_2120_, lean_object* v_declName_2121_, lean_object* v_as_2122_, lean_object* v_sz_2123_, lean_object* v_i_2124_, lean_object* v_b_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
size_t v_sz_boxed_2129_; size_t v_i_boxed_2130_; lean_object* v_res_2131_; 
v_sz_boxed_2129_ = lean_unbox_usize(v_sz_2123_);
lean_dec(v_sz_2123_);
v_i_boxed_2130_ = lean_unbox_usize(v_i_2124_);
lean_dec(v_i_2124_);
v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v___x_2120_, v_declName_2121_, v_as_2122_, v_sz_boxed_2129_, v_i_boxed_2130_, v_b_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_as_2122_);
lean_dec_ref(v___x_2120_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(lean_object* v_a_2132_, lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_box(0);
return v___x_2134_;
}
else
{
lean_object* v_key_2135_; lean_object* v_value_2136_; lean_object* v_tail_2137_; uint8_t v___x_2138_; 
v_key_2135_ = lean_ctor_get(v_x_2133_, 0);
v_value_2136_ = lean_ctor_get(v_x_2133_, 1);
v_tail_2137_ = lean_ctor_get(v_x_2133_, 2);
v___x_2138_ = lean_name_eq(v_key_2135_, v_a_2132_);
if (v___x_2138_ == 0)
{
v_x_2133_ = v_tail_2137_;
goto _start;
}
else
{
lean_object* v___x_2140_; 
lean_inc(v_value_2136_);
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_value_2136_);
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec(v_a_2141_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_buckets_2146_; lean_object* v___x_2147_; uint64_t v___y_2149_; 
v_buckets_2146_ = lean_ctor_get(v_m_2144_, 1);
v___x_2147_ = lean_array_get_size(v_buckets_2146_);
if (lean_obj_tag(v_a_2145_) == 0)
{
uint64_t v___x_2163_; 
v___x_2163_ = 1723ULL;
v___y_2149_ = v___x_2163_;
goto v___jp_2148_;
}
else
{
uint64_t v_hash_2164_; 
v_hash_2164_ = lean_ctor_get_uint64(v_a_2145_, sizeof(void*)*2);
v___y_2149_ = v_hash_2164_;
goto v___jp_2148_;
}
v___jp_2148_:
{
uint64_t v___x_2150_; uint64_t v___x_2151_; uint64_t v_fold_2152_; uint64_t v___x_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2150_ = 32ULL;
v___x_2151_ = lean_uint64_shift_right(v___y_2149_, v___x_2150_);
v_fold_2152_ = lean_uint64_xor(v___y_2149_, v___x_2151_);
v___x_2153_ = 16ULL;
v___x_2154_ = lean_uint64_shift_right(v_fold_2152_, v___x_2153_);
v___x_2155_ = lean_uint64_xor(v_fold_2152_, v___x_2154_);
v___x_2156_ = lean_uint64_to_usize(v___x_2155_);
v___x_2157_ = lean_usize_of_nat(v___x_2147_);
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_sub(v___x_2157_, v___x_2158_);
v___x_2160_ = lean_usize_land(v___x_2156_, v___x_2159_);
v___x_2161_ = lean_array_uget_borrowed(v_buckets_2146_, v___x_2160_);
v___x_2162_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2145_, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_m_2165_);
return v_res_2167_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__1));
v___x_2171_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__0));
v___x_2172_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(lean_object* v_declName_2175_, uint8_t v_isMeta_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v_env_2184_; lean_object* v___y_2186_; lean_object* v___x_2199_; 
v___x_2180_ = lean_st_ref_get(v___y_2178_);
v_env_2184_ = lean_ctor_get(v___x_2180_, 0);
lean_inc_ref(v_env_2184_);
lean_dec(v___x_2180_);
v___x_2199_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2184_, v_declName_2175_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_dec_ref(v_env_2184_);
lean_dec(v_declName_2175_);
goto v___jp_2181_;
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v_modules_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_val_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = l_Lean_Environment_header(v_env_2184_);
v_modules_2202_ = lean_ctor_get(v___x_2201_, 3);
lean_inc_ref(v_modules_2202_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = lean_array_get_size(v_modules_2202_);
v___x_2204_ = lean_nat_dec_lt(v_val_2200_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec_ref(v_modules_2202_);
lean_dec(v_val_2200_);
lean_dec_ref(v_env_2184_);
lean_dec(v_declName_2175_);
goto v___jp_2181_;
}
else
{
lean_object* v___x_2205_; lean_object* v_env_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___y_2210_; 
v___x_2205_ = lean_st_ref_get(v___y_2178_);
v_env_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc_ref(v_env_2206_);
lean_dec(v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__2);
v___x_2208_ = lean_array_fget(v_modules_2202_, v_val_2200_);
lean_dec(v_val_2200_);
lean_dec_ref(v_modules_2202_);
if (v_isMeta_2176_ == 0)
{
lean_dec_ref(v_env_2206_);
v___y_2210_ = v_isMeta_2176_;
goto v___jp_2209_;
}
else
{
uint8_t v___x_2221_; 
lean_inc(v_declName_2175_);
v___x_2221_ = l_Lean_isMarkedMeta(v_env_2206_, v_declName_2175_);
if (v___x_2221_ == 0)
{
v___y_2210_ = v_isMeta_2176_;
goto v___jp_2209_;
}
else
{
uint8_t v___x_2222_; 
v___x_2222_ = 0;
v___y_2210_ = v___x_2222_;
goto v___jp_2209_;
}
}
v___jp_2209_:
{
lean_object* v_toImport_2211_; lean_object* v_module_2212_; lean_object* v___x_2213_; 
v_toImport_2211_ = lean_ctor_get(v___x_2208_, 0);
lean_inc_ref(v_toImport_2211_);
lean_dec(v___x_2208_);
v_module_2212_ = lean_ctor_get(v_toImport_2211_, 0);
lean_inc(v_module_2212_);
lean_dec_ref(v_toImport_2211_);
lean_inc(v_declName_2175_);
v___x_2213_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4(v_module_2212_, v___y_2210_, v_declName_2175_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2213_, 1);
v___x_2214_ = l_Lean_indirectModUseExt;
v___x_2215_ = lean_box(1);
v___x_2216_ = lean_box(0);
lean_inc_ref(v_env_2184_);
v___x_2217_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2207_, v___x_2214_, v_env_2184_, v___x_2215_, v___x_2216_);
v___x_2218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2217_, v_declName_2175_);
lean_dec(v___x_2217_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2___closed__3));
v___y_2186_ = v___x_2219_;
goto v___jp_2185_;
}
else
{
lean_object* v_val_2220_; 
v_val_2220_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v___x_2218_, 1);
v___y_2186_ = v_val_2220_;
goto v___jp_2185_;
}
}
else
{
lean_dec_ref(v_env_2184_);
lean_dec(v_declName_2175_);
return v___x_2213_;
}
}
}
}
v___jp_2181_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
v___jp_2185_:
{
lean_object* v___x_2187_; size_t v_sz_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_box(0);
v_sz_2188_ = lean_array_size(v___y_2186_);
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__5(v_env_2184_, v_declName_2175_, v___y_2186_, v_sz_2188_, v___x_2189_, v___x_2187_, v___y_2177_, v___y_2178_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_env_2184_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2198_);
v___x_2192_ = v___x_2190_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v___x_2190_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2187_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2187_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
return v___x_2190_;
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
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__30_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = lean_box(1);
v___x_2283_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2284_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
lean_ctor_set(v___x_2285_, 2, v___x_2282_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
lean_ctor_set(v___x_2290_, 2, v___x_2289_);
lean_ctor_set(v___x_2290_, 3, v___x_2289_);
lean_ctor_set(v___x_2290_, 4, v___x_2288_);
lean_ctor_set(v___x_2290_, 5, v___x_2288_);
lean_ctor_set(v___x_2290_, 6, v___x_2288_);
lean_ctor_set(v___x_2290_, 7, v___x_2288_);
lean_ctor_set(v___x_2290_, 8, v___x_2288_);
lean_ctor_set(v___x_2290_, 9, v___x_2288_);
lean_ctor_set(v___x_2290_, 10, v___x_2288_);
return v___x_2290_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2292_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
lean_ctor_set(v___x_2292_, 2, v___x_2291_);
lean_ctor_set(v___x_2292_, 3, v___x_2291_);
lean_ctor_set(v___x_2292_, 4, v___x_2291_);
lean_ctor_set(v___x_2292_, 5, v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__31_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
lean_ctor_set(v___x_2294_, 2, v___x_2293_);
lean_ctor_set(v___x_2294_, 3, v___x_2293_);
lean_ctor_set(v___x_2294_, 4, v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__37_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2297_ = l_Lean_stringToMessageData(v___x_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__39_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2300_ = l_Lean_stringToMessageData(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__41_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__43_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__45_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2309_ = l_Lean_stringToMessageData(v___x_2308_);
return v___x_2309_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__47_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2312_ = l_Lean_stringToMessageData(v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__49_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__51_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2318_ = l_Lean_stringToMessageData(v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__53_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2321_ = l_Lean_stringToMessageData(v___x_2320_);
return v___x_2321_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__55_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2324_ = l_Lean_stringToMessageData(v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__57_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__59_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__61_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___f_2336_, uint8_t v___x_2337_, lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v_a_2340_, lean_object* v_declName_2341_, lean_object* v_stx_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v_hint_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; 
v___x_2352_ = l_Lean_Name_mkStr2(v___x_2334_, v___x_2335_);
lean_inc(v_stx_2342_);
v___x_2353_ = l_Lean_Syntax_isOfKind(v_stx_2342_, v___x_2352_);
lean_dec(v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec(v_stx_2342_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2462_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2463_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2462_, v___y_2343_, v___y_2344_);
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v_val_2475_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2512_; lean_object* v___y_2513_; uint8_t v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; uint8_t v_a_2522_; lean_object* v___y_2537_; uint8_t v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2582_; uint8_t v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v_msg_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; uint8_t v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v_a_2616_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v_a_2760_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v_since_x3f_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_typeChanged_x3f_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2816_; lean_object* v_text_x3f_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v_id_x3f_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2842_ = l_Lean_Syntax_getArg(v_stx_2342_, v___x_2465_);
v___x_2843_ = l_Lean_Syntax_isNone(v___x_2842_);
if (v___x_2843_ == 0)
{
uint8_t v___x_2844_; 
lean_inc(v___x_2842_);
v___x_2844_ = l_Lean_Syntax_matchesNull(v___x_2842_, v___x_2465_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec(v___x_2842_);
lean_dec(v_stx_2342_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2845_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2846_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2845_, v___y_2343_, v___y_2344_);
return v___x_2846_;
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_Lean_Syntax_getArg(v___x_2842_, v___x_2464_);
lean_dec(v___x_2842_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v_id_x3f_2830_ = v___x_2848_;
v___y_2831_ = v___y_2343_;
v___y_2832_ = v___y_2344_;
goto v___jp_2829_;
}
}
else
{
lean_object* v___x_2849_; 
lean_dec(v___x_2842_);
v___x_2849_ = lean_box(0);
v_id_x3f_2830_ = v___x_2849_;
v___y_2831_ = v___y_2343_;
v___y_2832_ = v___y_2344_;
goto v___jp_2829_;
}
v___jp_2466_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2476_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__20_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2477_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__22_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__26_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___f_2336_);
v___x_2481_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2477_);
lean_ctor_set(v___x_2481_, 1, v___x_2478_);
lean_ctor_set(v___x_2481_, 2, v___x_2478_);
lean_ctor_set(v___x_2481_, 3, v___x_2478_);
lean_ctor_set(v___x_2481_, 4, v___x_2479_);
lean_ctor_set(v___x_2481_, 5, v___x_2480_);
lean_inc(v_val_2475_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_val_2475_);
lean_ctor_set(v___x_2482_, 1, v_val_2475_);
v___x_2483_ = l_Lean_Syntax_ofRange(v___x_2482_, v___x_2353_);
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
v___x_2485_ = 4;
v___x_2486_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2486_, 0, v___x_2481_);
lean_ctor_set(v___x_2486_, 1, v___x_2484_);
lean_ctor_set(v___x_2486_, 2, v___x_2478_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*3, v___x_2485_);
v___x_2487_ = lean_mk_empty_array_with_capacity(v___x_2465_);
v___x_2488_ = lean_array_push(v___x_2487_, v___x_2486_);
v___x_2489_ = l_Lean_MessageData_hint(v___x_2476_, v___x_2488_, v___x_2478_, v___x_2478_, v___x_2337_, v___y_2467_, v___y_2472_);
lean_dec_ref(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___y_2422_ = v___y_2468_;
v___y_2423_ = v___y_2470_;
v___y_2424_ = v___y_2469_;
v___y_2425_ = v___y_2471_;
v___y_2426_ = v___y_2473_;
v___y_2427_ = v___y_2474_;
v_hint_2428_ = v_a_2490_;
v___y_2429_ = v___y_2467_;
v___y_2430_ = v___y_2472_;
goto v___jp_2421_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2489_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
v___jp_2499_:
{
if (lean_obj_tag(v___y_2503_) == 0)
{
lean_dec_ref(v___f_2336_);
v___y_2453_ = v___y_2500_;
v___y_2454_ = v___y_2501_;
v___y_2455_ = v___y_2503_;
v___y_2456_ = v___y_2502_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2506_;
v___y_2460_ = v___y_2507_;
goto v___jp_2452_;
}
else
{
lean_object* v_val_2508_; lean_object* v___x_2509_; 
v_val_2508_ = lean_ctor_get(v___y_2503_, 0);
v___x_2509_ = l_Lean_Syntax_getTailPos_x3f(v_val_2508_, v___x_2353_);
if (lean_obj_tag(v___x_2509_) == 1)
{
lean_object* v_val_2510_; 
v_val_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2467_ = v___y_2500_;
v___y_2468_ = v___y_2501_;
v___y_2469_ = v___y_2503_;
v___y_2470_ = v___y_2502_;
v___y_2471_ = v___y_2504_;
v___y_2472_ = v___y_2505_;
v___y_2473_ = v___y_2506_;
v___y_2474_ = v___y_2507_;
v_val_2475_ = v_val_2510_;
goto v___jp_2466_;
}
else
{
lean_dec(v___x_2509_);
lean_dec_ref(v___f_2336_);
v___y_2453_ = v___y_2500_;
v___y_2454_ = v___y_2501_;
v___y_2455_ = v___y_2503_;
v___y_2456_ = v___y_2502_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2506_;
v___y_2460_ = v___y_2507_;
goto v___jp_2452_;
}
}
}
v___jp_2511_:
{
if (v_a_2522_ == 0)
{
if (lean_obj_tag(v___y_2518_) == 0)
{
if (v___y_2514_ == 0)
{
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2513_;
v___y_2406_ = v___y_2516_;
v___y_2407_ = v___y_2515_;
v___y_2408_ = v___y_2521_;
v___y_2409_ = v___y_2512_;
v___y_2410_ = v___y_2519_;
goto v___jp_2404_;
}
else
{
if (lean_obj_tag(v___y_2521_) == 0)
{
v___y_2500_ = v___y_2512_;
v___y_2501_ = v___y_2513_;
v___y_2502_ = v___y_2515_;
v___y_2503_ = v___y_2516_;
v___y_2504_ = v___y_2517_;
v___y_2505_ = v___y_2519_;
v___y_2506_ = v___y_2520_;
v___y_2507_ = v___y_2521_;
goto v___jp_2499_;
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2524_; 
v_val_2523_ = lean_ctor_get(v___y_2521_, 0);
v___x_2524_ = l_Lean_Syntax_getTailPos_x3f(v_val_2523_, v___x_2353_);
if (lean_obj_tag(v___x_2524_) == 0)
{
v___y_2500_ = v___y_2512_;
v___y_2501_ = v___y_2513_;
v___y_2502_ = v___y_2515_;
v___y_2503_ = v___y_2516_;
v___y_2504_ = v___y_2517_;
v___y_2505_ = v___y_2519_;
v___y_2506_ = v___y_2520_;
v___y_2507_ = v___y_2521_;
goto v___jp_2499_;
}
else
{
lean_object* v_val_2525_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___y_2467_ = v___y_2512_;
v___y_2468_ = v___y_2513_;
v___y_2469_ = v___y_2516_;
v___y_2470_ = v___y_2515_;
v___y_2471_ = v___y_2517_;
v___y_2472_ = v___y_2519_;
v___y_2473_ = v___y_2520_;
v___y_2474_ = v___y_2521_;
v_val_2475_ = v_val_2525_;
goto v___jp_2466_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_2518_, 1);
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2513_;
v___y_2406_ = v___y_2516_;
v___y_2407_ = v___y_2515_;
v___y_2408_ = v___y_2521_;
v___y_2409_ = v___y_2512_;
v___y_2410_ = v___y_2519_;
goto v___jp_2404_;
}
}
else
{
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___f_2336_);
if (lean_obj_tag(v___y_2518_) == 0)
{
v___y_2405_ = v___y_2513_;
v___y_2406_ = v___y_2516_;
v___y_2407_ = v___y_2515_;
v___y_2408_ = v___y_2521_;
v___y_2409_ = v___y_2512_;
v___y_2410_ = v___y_2519_;
goto v___jp_2404_;
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec_ref_known(v___y_2518_, 1);
v___x_2526_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__29_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2527_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2526_, v___y_2512_, v___y_2519_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_dec_ref_known(v___x_2527_, 1);
v___y_2405_ = v___y_2513_;
v___y_2406_ = v___y_2516_;
v___y_2407_ = v___y_2515_;
v___y_2408_ = v___y_2521_;
v___y_2409_ = v___y_2512_;
v___y_2410_ = v___y_2519_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___y_2521_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2513_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
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
}
}
v___jp_2536_:
{
lean_object* v___x_2547_; 
lean_inc_ref(v___y_2543_);
v___x_2547_ = l_Lean_Environment_find_x3f(v___y_2543_, v_declName_2341_, v___x_2337_);
if (lean_obj_tag(v___x_2547_) == 1)
{
lean_object* v_val_2548_; lean_object* v___x_2549_; 
v_val_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = l_Lean_Environment_find_x3f(v___y_2543_, v___y_2542_, v___x_2337_);
if (lean_obj_tag(v___x_2549_) == 1)
{
lean_object* v_val_2550_; uint8_t v___x_2551_; uint8_t v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; uint64_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_val_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = 1;
v___x_2552_ = 0;
v___x_2553_ = 2;
v___x_2554_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2554_, 0, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 1, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 2, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 3, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 4, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 5, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 6, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 7, v___x_2337_);
lean_ctor_set_uint8(v___x_2554_, 8, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 9, v___x_2551_);
lean_ctor_set_uint8(v___x_2554_, 10, v___x_2552_);
lean_ctor_set_uint8(v___x_2554_, 11, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 12, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 13, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 14, v___x_2553_);
lean_ctor_set_uint8(v___x_2554_, 15, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 16, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 17, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 18, v___y_2538_);
lean_ctor_set_uint8(v___x_2554_, 19, v___x_2337_);
v___x_2555_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set_uint64(v___x_2556_, sizeof(void*)*1, v___x_2555_);
v___x_2557_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2558_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2560_ = lean_box(0);
lean_inc(v___x_2338_);
v___x_2561_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2561_, 0, v___x_2556_);
lean_ctor_set(v___x_2561_, 1, v___x_2338_);
lean_ctor_set(v___x_2561_, 2, v___x_2558_);
lean_ctor_set(v___x_2561_, 3, v___x_2559_);
lean_ctor_set(v___x_2561_, 4, v___x_2560_);
lean_ctor_set(v___x_2561_, 5, v___x_2464_);
lean_ctor_set(v___x_2561_, 6, v___x_2560_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*7, v___x_2337_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*7 + 1, v___x_2337_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*7 + 2, v___x_2337_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*7 + 3, v___x_2353_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2563_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2564_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2562_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
lean_ctor_set(v___x_2565_, 2, v___x_2338_);
lean_ctor_set(v___x_2565_, 3, v___x_2557_);
lean_ctor_set(v___x_2565_, 4, v___x_2564_);
v___x_2566_ = lean_st_mk_ref(v___x_2565_);
v___x_2567_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_2548_, v_val_2550_, v___x_2561_, v___x_2566_, v___y_2545_, v___y_2546_);
lean_dec_ref_known(v___x_2561_, 7);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = lean_st_ref_get(v___x_2566_);
lean_dec(v___x_2566_);
lean_dec(v___x_2569_);
v___x_2570_ = lean_unbox(v_a_2568_);
lean_dec(v_a_2568_);
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2539_;
v___y_2517_ = v_val_2550_;
v___y_2518_ = v___y_2541_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v_val_2548_;
v___y_2521_ = v___y_2544_;
v_a_2522_ = v___x_2570_;
goto v___jp_2511_;
}
else
{
lean_dec(v___x_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2571_; uint8_t v___x_2572_; 
v_a_2571_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2572_ = lean_unbox(v_a_2571_);
lean_dec(v_a_2571_);
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2539_;
v___y_2517_ = v_val_2550_;
v___y_2518_ = v___y_2541_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v_val_2548_;
v___y_2521_ = v___y_2544_;
v_a_2522_ = v___x_2572_;
goto v___jp_2511_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_val_2550_);
lean_dec(v_val_2548_);
lean_dec(v___y_2544_);
lean_dec(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec(v___y_2537_);
lean_dec_ref(v___f_2336_);
v_a_2573_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2567_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2567_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_dec(v___x_2549_);
lean_dec(v_val_2548_);
lean_dec(v___y_2541_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2537_;
v___y_2406_ = v___y_2539_;
v___y_2407_ = v___y_2540_;
v___y_2408_ = v___y_2544_;
v___y_2409_ = v___y_2545_;
v___y_2410_ = v___y_2546_;
goto v___jp_2404_;
}
}
else
{
lean_dec(v___x_2547_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2537_;
v___y_2406_ = v___y_2539_;
v___y_2407_ = v___y_2540_;
v___y_2408_ = v___y_2544_;
v___y_2409_ = v___y_2545_;
v___y_2410_ = v___y_2546_;
goto v___jp_2404_;
}
}
v___jp_2581_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v_msg_2590_, v___y_2591_, v___y_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_dec_ref_known(v___x_2593_, 1);
v___y_2537_ = v___y_2582_;
v___y_2538_ = v___y_2583_;
v___y_2539_ = v___y_2585_;
v___y_2540_ = v___y_2584_;
v___y_2541_ = v___y_2586_;
v___y_2542_ = v___y_2588_;
v___y_2543_ = v___y_2587_;
v___y_2544_ = v___y_2589_;
v___y_2545_ = v___y_2591_;
v___y_2546_ = v___y_2592_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2582_);
lean_dec(v_declName_2341_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
v___jp_2602_:
{
if (lean_obj_tag(v_a_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2647_; 
v_val_2617_ = lean_ctor_get(v_a_2616_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2616_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2619_ = v_a_2616_;
v_isShared_2620_ = v_isSharedCheck_2647_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_val_2617_);
lean_dec(v_a_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2647_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2621_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__38_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___y_2609_);
v___x_2623_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__40_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = l_Lean_Name_toString(v_val_2617_, v___x_2353_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
lean_ctor_set(v___x_2628_, 2, v___x_2627_);
lean_ctor_set(v___x_2628_, 3, v___x_2627_);
lean_ctor_set(v___x_2628_, 4, v___x_2627_);
lean_ctor_set(v___x_2628_, 5, v___x_2627_);
v___x_2629_ = 0;
v___x_2630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2627_);
lean_ctor_set(v___x_2630_, 2, v___x_2627_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*3, v___x_2629_);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2465_);
v___x_2632_ = lean_array_push(v___x_2631_, v___x_2630_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___y_2604_);
v___x_2634_ = v___x_2619_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___y_2604_);
v___x_2634_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_MessageData_hint(v___x_2624_, v___x_2632_, v___x_2634_, v___x_2627_, v___x_2337_, v___y_2610_, v___y_2603_);
lean_dec_ref(v___x_2632_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___y_2607_);
lean_ctor_set(v___x_2637_, 1, v_a_2636_);
v___y_2582_ = v___y_2605_;
v___y_2583_ = v___y_2606_;
v___y_2584_ = v___y_2611_;
v___y_2585_ = v___y_2612_;
v___y_2586_ = v___y_2608_;
v___y_2587_ = v___y_2613_;
v___y_2588_ = v___y_2614_;
v___y_2589_ = v___y_2615_;
v_msg_2590_ = v___x_2637_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___y_2603_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2605_);
lean_dec(v_declName_2341_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2638_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2635_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2635_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2616_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2604_);
v___y_2582_ = v___y_2605_;
v___y_2583_ = v___y_2606_;
v___y_2584_ = v___y_2611_;
v___y_2585_ = v___y_2612_;
v___y_2586_ = v___y_2608_;
v___y_2587_ = v___y_2613_;
v___y_2588_ = v___y_2614_;
v___y_2589_ = v___y_2615_;
v_msg_2590_ = v___y_2607_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___y_2603_;
goto v___jp_2581_;
}
}
v___jp_2648_:
{
if (lean_obj_tag(v___y_2649_) == 1)
{
lean_object* v_val_2656_; lean_object* v___x_2657_; 
v_val_2656_ = lean_ctor_get(v___y_2649_, 0);
lean_inc(v_val_2656_);
v___x_2657_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2(v_val_2656_, v___x_2337_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2658_; lean_object* v_a_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_dec_ref_known(v___x_2657_, 1);
v___x_2658_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3(v___y_2654_, v___y_2655_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = l_Lean_Linter_linter_deprecated;
v___x_2661_ = l_Lean_Linter_getLinterValue(v___x_2660_, v_a_2659_);
lean_dec(v_a_2659_);
if (v___x_2661_ == 0)
{
lean_dec(v___y_2652_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2649_;
v___y_2406_ = v___y_2651_;
v___y_2407_ = v___y_2650_;
v___y_2408_ = v___y_2653_;
v___y_2409_ = v___y_2654_;
v___y_2410_ = v___y_2655_;
goto v___jp_2404_;
}
else
{
lean_object* v___x_2662_; lean_object* v_env_2663_; lean_object* v_options_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
lean_inc(v_val_2656_);
v___x_2662_ = lean_st_ref_get(v___y_2655_);
v_env_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_ref(v_env_2663_);
lean_dec(v___x_2662_);
v_options_2664_ = lean_ctor_get(v___y_2654_, 2);
v___x_2665_ = l_Lean_Linter_linter_deprecated_deprecatedTarget;
v___x_2666_ = l_Lean_Option_get___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__4(v_options_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v___x_2339_);
v___y_2537_ = v___y_2649_;
v___y_2538_ = v___x_2661_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v___y_2650_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2656_;
v___y_2543_ = v_env_2663_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
v___y_2546_ = v___y_2655_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2667_; 
lean_inc(v_val_2656_);
lean_inc_ref(v_env_2663_);
v___x_2667_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v___x_2339_, v_a_2340_, v___x_2337_, v_env_2663_, v_val_2656_);
if (lean_obj_tag(v___x_2667_) == 1)
{
lean_object* v_val_2668_; lean_object* v_name_2669_; lean_object* v_newName_x3f_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_val_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v_name_2669_ = lean_ctor_get(v___x_2665_, 0);
v_newName_x3f_2670_ = lean_ctor_get(v_val_2668_, 0);
lean_inc(v_newName_x3f_2670_);
lean_dec(v_val_2668_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__42_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_name_2669_);
v___x_2672_ = l_Lean_MessageData_ofName(v_name_2669_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__44_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_MessageData_note(v___x_2675_);
if (lean_obj_tag(v_newName_x3f_2670_) == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2677_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2656_);
v___x_2678_ = l_Lean_MessageData_ofConstName(v_val_2656_, v___x_2353_);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__48_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_inc(v_declName_2341_);
v___x_2682_ = l_Lean_MessageData_ofConstName(v_declName_2341_, v___x_2353_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__50_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v___x_2676_);
v___x_2687_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2686_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_dec_ref_known(v___x_2687_, 1);
v___y_2537_ = v___y_2649_;
v___y_2538_ = v___x_2661_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v___y_2650_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2656_;
v___y_2543_ = v_env_2663_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
v___y_2546_ = v___y_2655_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v_env_2663_);
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v_val_2656_);
lean_dec(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v_declName_2341_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_val_2696_; uint8_t v___x_2697_; 
v_val_2696_ = lean_ctor_get(v_newName_x3f_2670_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v_newName_x3f_2670_, 1);
v___x_2697_ = lean_name_eq(v_val_2696_, v_val_2656_);
if (v___x_2697_ == 0)
{
if (v___x_2666_ == 0)
{
lean_dec(v_val_2696_);
lean_dec_ref(v___x_2676_);
v___y_2537_ = v___y_2649_;
v___y_2538_ = v___x_2661_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v___y_2650_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2656_;
v___y_2543_ = v_env_2663_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
v___y_2546_ = v___y_2655_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2698_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
lean_inc(v_val_2656_);
v___x_2699_ = l_Lean_MessageData_ofConstName(v_val_2656_, v___x_2353_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__52_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc(v_val_2696_);
v___x_2703_ = l_Lean_MessageData_ofConstName(v_val_2696_, v___x_2353_);
lean_inc_ref_n(v___x_2703_, 2);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__54_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc(v_declName_2341_);
v___x_2707_ = l_Lean_MessageData_ofConstName(v_declName_2341_, v___x_2353_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__56_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2703_);
v___x_2712_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2676_);
if (lean_obj_tag(v___y_2651_) == 1)
{
lean_object* v_val_2715_; lean_object* v___x_2716_; 
v_val_2715_ = lean_ctor_get(v___y_2651_, 0);
v___x_2716_ = l_Lean_Syntax_getRange_x3f(v_val_2715_, v___x_2353_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref(v___x_2703_);
lean_dec(v_val_2696_);
v___y_2582_ = v___y_2649_;
v___y_2583_ = v___x_2661_;
v___y_2584_ = v___y_2650_;
v___y_2585_ = v___y_2651_;
v___y_2586_ = v___y_2652_;
v___y_2587_ = v_env_2663_;
v___y_2588_ = v_val_2656_;
v___y_2589_ = v___y_2653_;
v_msg_2590_ = v___x_2714_;
v___y_2591_ = v___y_2654_;
v___y_2592_ = v___y_2655_;
goto v___jp_2581_;
}
else
{
uint8_t v___x_2717_; uint8_t v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; uint64_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_inc(v_val_2715_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2717_ = 1;
v___x_2718_ = 0;
v___x_2719_ = 2;
v___x_2720_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_2720_, 0, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 1, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 2, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 3, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 4, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 5, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 6, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 7, v___x_2697_);
lean_ctor_set_uint8(v___x_2720_, 8, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 9, v___x_2717_);
lean_ctor_set_uint8(v___x_2720_, 10, v___x_2718_);
lean_ctor_set_uint8(v___x_2720_, 11, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 12, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 13, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 14, v___x_2719_);
lean_ctor_set_uint8(v___x_2720_, 15, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 16, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 17, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 18, v___x_2666_);
lean_ctor_set_uint8(v___x_2720_, 19, v___x_2697_);
v___x_2721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint64(v___x_2722_, sizeof(void*)*1, v___x_2721_);
v___x_2723_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2724_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__32_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2725_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__33_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2726_ = lean_box(0);
lean_inc_n(v___x_2338_, 2);
v___x_2727_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2727_, 0, v___x_2722_);
lean_ctor_set(v___x_2727_, 1, v___x_2338_);
lean_ctor_set(v___x_2727_, 2, v___x_2724_);
lean_ctor_set(v___x_2727_, 3, v___x_2725_);
lean_ctor_set(v___x_2727_, 4, v___x_2726_);
lean_ctor_set(v___x_2727_, 5, v___x_2464_);
lean_ctor_set(v___x_2727_, 6, v___x_2726_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*7, v___x_2337_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*7 + 1, v___x_2337_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*7 + 2, v___x_2337_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*7 + 3, v___x_2353_);
v___x_2728_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__34_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__35_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2730_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__36_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2728_);
lean_ctor_set(v___x_2731_, 1, v___x_2729_);
lean_ctor_set(v___x_2731_, 2, v___x_2338_);
lean_ctor_set(v___x_2731_, 3, v___x_2723_);
lean_ctor_set(v___x_2731_, 4, v___x_2730_);
v___x_2732_ = lean_st_mk_ref(v___x_2731_);
v___x_2733_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_val_2696_, v___x_2337_, v___x_2727_, v___x_2732_, v___y_2654_, v___y_2655_);
lean_dec_ref_known(v___x_2727_, 7);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_st_ref_get(v___x_2732_);
lean_dec(v___x_2732_);
lean_dec(v___x_2735_);
v___y_2603_ = v___y_2655_;
v___y_2604_ = v_val_2715_;
v___y_2605_ = v___y_2649_;
v___y_2606_ = v___x_2661_;
v___y_2607_ = v___x_2714_;
v___y_2608_ = v___y_2652_;
v___y_2609_ = v___x_2703_;
v___y_2610_ = v___y_2654_;
v___y_2611_ = v___y_2650_;
v___y_2612_ = v___y_2651_;
v___y_2613_ = v_env_2663_;
v___y_2614_ = v_val_2656_;
v___y_2615_ = v___y_2653_;
v_a_2616_ = v_a_2734_;
goto v___jp_2602_;
}
else
{
lean_dec(v___x_2732_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2733_, 1);
v___y_2603_ = v___y_2655_;
v___y_2604_ = v_val_2715_;
v___y_2605_ = v___y_2649_;
v___y_2606_ = v___x_2661_;
v___y_2607_ = v___x_2714_;
v___y_2608_ = v___y_2652_;
v___y_2609_ = v___x_2703_;
v___y_2610_ = v___y_2654_;
v___y_2611_ = v___y_2650_;
v___y_2612_ = v___y_2651_;
v___y_2613_ = v_env_2663_;
v___y_2614_ = v_val_2656_;
v___y_2615_ = v___y_2653_;
v_a_2616_ = v_a_2736_;
goto v___jp_2602_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref_known(v___y_2651_, 1);
lean_dec(v_val_2715_);
lean_dec_ref_known(v___x_2714_, 2);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v_env_2663_);
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v_val_2656_);
lean_dec(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2650_);
lean_dec(v_declName_2341_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2737_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2733_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2733_);
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
lean_dec_ref(v___x_2703_);
lean_dec(v_val_2696_);
v___y_2582_ = v___y_2649_;
v___y_2583_ = v___x_2661_;
v___y_2584_ = v___y_2650_;
v___y_2585_ = v___y_2651_;
v___y_2586_ = v___y_2652_;
v___y_2587_ = v_env_2663_;
v___y_2588_ = v_val_2656_;
v___y_2589_ = v___y_2653_;
v_msg_2590_ = v___x_2714_;
v___y_2591_ = v___y_2654_;
v___y_2592_ = v___y_2655_;
goto v___jp_2581_;
}
}
}
else
{
lean_dec(v_val_2696_);
lean_dec_ref(v___x_2676_);
v___y_2537_ = v___y_2649_;
v___y_2538_ = v___x_2661_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v___y_2650_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2656_;
v___y_2543_ = v_env_2663_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
v___y_2546_ = v___y_2655_;
goto v___jp_2536_;
}
}
}
else
{
lean_dec(v___x_2667_);
v___y_2537_ = v___y_2649_;
v___y_2538_ = v___x_2661_;
v___y_2539_ = v___y_2651_;
v___y_2540_ = v___y_2650_;
v___y_2541_ = v___y_2652_;
v___y_2542_ = v_val_2656_;
v___y_2543_ = v_env_2663_;
v___y_2544_ = v___y_2653_;
v___y_2545_ = v___y_2654_;
v___y_2546_ = v___y_2655_;
goto v___jp_2536_;
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref_known(v___y_2649_, 1);
lean_dec(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2745_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2657_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2657_);
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
lean_dec(v___y_2652_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___y_2405_ = v___y_2649_;
v___y_2406_ = v___y_2651_;
v___y_2407_ = v___y_2650_;
v___y_2408_ = v___y_2653_;
v___y_2409_ = v___y_2654_;
v___y_2410_ = v___y_2655_;
goto v___jp_2404_;
}
}
v___jp_2753_:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
lean_inc(v_declName_2341_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_declName_2341_);
v___x_2762_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__6(v_a_2760_, v___x_2761_);
lean_dec_ref_known(v___x_2761_, 1);
if (v___x_2762_ == 0)
{
v___y_2649_ = v_a_2760_;
v___y_2650_ = v___y_2754_;
v___y_2651_ = v___y_2755_;
v___y_2652_ = v___y_2757_;
v___y_2653_ = v___y_2759_;
v___y_2654_ = v___y_2756_;
v___y_2655_ = v___y_2758_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2757_);
lean_dec(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2763_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__60_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2764_ = l_Lean_MessageData_ofConstName(v_declName_2341_, v___x_2353_);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__62_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2767_, v___y_2756_, v___y_2758_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
v___jp_2777_:
{
if (lean_obj_tag(v___y_2778_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_box(0);
v___y_2754_ = v_since_x3f_2781_;
v___y_2755_ = v___y_2778_;
v___y_2756_ = v___y_2782_;
v___y_2757_ = v___y_2779_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2780_;
v_a_2760_ = v___x_2784_;
goto v___jp_2753_;
}
else
{
lean_object* v_val_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_val_2785_ = lean_ctor_get(v___y_2778_, 0);
v___x_2786_ = lean_box(0);
lean_inc(v_val_2785_);
v___x_2787_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_2785_, v___x_2786_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_a_2788_);
v___y_2754_ = v_since_x3f_2781_;
v___y_2755_ = v___y_2778_;
v___y_2756_ = v___y_2782_;
v___y_2757_ = v___y_2779_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2780_;
v_a_2760_ = v___x_2789_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref_known(v___y_2778_, 1);
lean_dec(v_since_x3f_2781_);
lean_dec(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v_a_2790_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2787_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2787_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
v___jp_2798_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2805_ = lean_unsigned_to_nat(4u);
v___x_2806_ = l_Lean_Syntax_getArg(v_stx_2342_, v___x_2805_);
lean_dec(v_stx_2342_);
v___x_2807_ = l_Lean_Syntax_isNone(v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2806_);
v___x_2809_ = l_Lean_Syntax_matchesNull(v___x_2806_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec(v___x_2806_);
lean_dec(v_typeChanged_x3f_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2811_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2810_, v___y_2803_, v___y_2804_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = l_Lean_Syntax_getArg(v___x_2806_, v___y_2799_);
lean_dec(v___x_2806_);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
v___y_2778_ = v___y_2800_;
v___y_2779_ = v_typeChanged_x3f_2802_;
v___y_2780_ = v___y_2801_;
v_since_x3f_2781_ = v___x_2813_;
v___y_2782_ = v___y_2803_;
v___y_2783_ = v___y_2804_;
goto v___jp_2777_;
}
}
else
{
lean_object* v___x_2814_; 
lean_dec(v___x_2806_);
v___x_2814_ = lean_box(0);
v___y_2778_ = v___y_2800_;
v___y_2779_ = v_typeChanged_x3f_2802_;
v___y_2780_ = v___y_2801_;
v_since_x3f_2781_ = v___x_2814_;
v___y_2782_ = v___y_2803_;
v___y_2783_ = v___y_2804_;
goto v___jp_2777_;
}
}
v___jp_2815_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2820_ = lean_unsigned_to_nat(3u);
v___x_2821_ = l_Lean_Syntax_getArg(v_stx_2342_, v___x_2820_);
v___x_2822_ = l_Lean_Syntax_isNone(v___x_2821_);
if (v___x_2822_ == 0)
{
uint8_t v___x_2823_; 
lean_inc(v___x_2821_);
v___x_2823_ = l_Lean_Syntax_matchesNull(v___x_2821_, v___x_2465_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v___x_2821_);
lean_dec(v_text_x3f_2817_);
lean_dec(v___y_2816_);
lean_dec(v_stx_2342_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2825_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2824_, v___y_2818_, v___y_2819_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = l_Lean_Syntax_getArg(v___x_2821_, v___x_2464_);
lean_dec(v___x_2821_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
v___y_2799_ = v___x_2820_;
v___y_2800_ = v___y_2816_;
v___y_2801_ = v_text_x3f_2817_;
v_typeChanged_x3f_2802_ = v___x_2827_;
v___y_2803_ = v___y_2818_;
v___y_2804_ = v___y_2819_;
goto v___jp_2798_;
}
}
else
{
lean_object* v___x_2828_; 
lean_dec(v___x_2821_);
v___x_2828_ = lean_box(0);
v___y_2799_ = v___x_2820_;
v___y_2800_ = v___y_2816_;
v___y_2801_ = v_text_x3f_2817_;
v_typeChanged_x3f_2802_ = v___x_2828_;
v___y_2803_ = v___y_2818_;
v___y_2804_ = v___y_2819_;
goto v___jp_2798_;
}
}
v___jp_2829_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2833_ = lean_unsigned_to_nat(2u);
v___x_2834_ = l_Lean_Syntax_getArg(v_stx_2342_, v___x_2833_);
v___x_2835_ = l_Lean_Syntax_isNone(v___x_2834_);
if (v___x_2835_ == 0)
{
uint8_t v___x_2836_; 
lean_inc(v___x_2834_);
v___x_2836_ = l_Lean_Syntax_matchesNull(v___x_2834_, v___x_2465_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec(v___x_2834_);
lean_dec(v_id_x3f_2830_);
lean_dec(v_stx_2342_);
lean_dec(v_declName_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___x_2338_);
lean_dec_ref(v___f_2336_);
v___x_2837_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__17_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2838_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v___x_2837_, v___y_2831_, v___y_2832_);
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Lean_Syntax_getArg(v___x_2834_, v___x_2464_);
lean_dec(v___x_2834_);
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
v___y_2816_ = v_id_x3f_2830_;
v_text_x3f_2817_ = v___x_2840_;
v___y_2818_ = v___y_2831_;
v___y_2819_ = v___y_2832_;
goto v___jp_2815_;
}
}
else
{
lean_object* v___x_2841_; 
lean_dec(v___x_2834_);
v___x_2841_ = lean_box(0);
v___y_2816_ = v_id_x3f_2830_;
v_text_x3f_2817_ = v___x_2841_;
v___y_2818_ = v___y_2831_;
v___y_2819_ = v___y_2832_;
goto v___jp_2815_;
}
}
}
v___jp_2346_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2347_);
lean_ctor_set(v___x_2350_, 1, v___y_2349_);
lean_ctor_set(v___x_2350_, 2, v___y_2348_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
v___jp_2354_:
{
if (lean_obj_tag(v___y_2357_) == 0)
{
if (v___x_2353_ == 0)
{
v___y_2347_ = v___y_2355_;
v___y_2348_ = v___y_2357_;
v___y_2349_ = v___y_2356_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2361_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2360_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_dec_ref_known(v___x_2361_, 1);
v___y_2347_ = v___y_2355_;
v___y_2348_ = v___y_2357_;
v___y_2349_ = v___y_2356_;
goto v___jp_2346_;
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v___y_2356_);
lean_dec(v___y_2355_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
v___y_2347_ = v___y_2355_;
v___y_2348_ = v___y_2357_;
v___y_2349_ = v___y_2356_;
goto v___jp_2346_;
}
}
v___jp_2370_:
{
if (lean_obj_tag(v___y_2373_) == 0)
{
if (v___x_2353_ == 0)
{
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2374_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2375_;
goto v___jp_2354_;
}
else
{
if (lean_obj_tag(v___y_2374_) == 0)
{
if (v___x_2353_ == 0)
{
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2374_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2375_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__5_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2378_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2377_, v___y_2371_, v___y_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_dec_ref_known(v___x_2378_, 1);
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2374_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2375_;
goto v___jp_2354_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v___y_2376_);
lean_dec(v___y_2372_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2374_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2375_;
goto v___jp_2354_;
}
}
}
else
{
lean_dec_ref_known(v___y_2373_, 1);
v___y_2355_ = v___y_2372_;
v___y_2356_ = v___y_2374_;
v___y_2357_ = v___y_2376_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2375_;
goto v___jp_2354_;
}
}
v___jp_2387_:
{
if (lean_obj_tag(v___y_2390_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_box(0);
v___y_2371_ = v___y_2389_;
v___y_2372_ = v___y_2388_;
v___y_2373_ = v___y_2391_;
v___y_2374_ = v___y_2393_;
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___x_2394_;
goto v___jp_2370_;
}
else
{
lean_object* v_val_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
v_val_2395_ = lean_ctor_get(v___y_2390_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___y_2390_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2397_ = v___y_2390_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_val_2395_);
lean_dec(v___y_2390_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = l_Lean_TSyntax_getString(v_val_2395_);
lean_dec(v_val_2395_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
v___y_2371_ = v___y_2389_;
v___y_2372_ = v___y_2388_;
v___y_2373_ = v___y_2391_;
v___y_2374_ = v___y_2393_;
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___x_2401_;
goto v___jp_2370_;
}
}
}
}
v___jp_2404_:
{
if (lean_obj_tag(v___y_2408_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_box(0);
v___y_2388_ = v___y_2405_;
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___y_2410_;
v___y_2393_ = v___x_2411_;
goto v___jp_2387_;
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_val_2412_ = lean_ctor_get(v___y_2408_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___y_2408_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2414_ = v___y_2408_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_val_2412_);
lean_dec(v___y_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_TSyntax_getString(v_val_2412_);
lean_dec(v_val_2412_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
v___y_2388_ = v___y_2405_;
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2407_;
v___y_2391_ = v___y_2406_;
v___y_2392_ = v___y_2410_;
v___y_2393_ = v___x_2418_;
goto v___jp_2387_;
}
}
}
}
v___jp_2421_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2431_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2432_ = l_Lean_ConstantInfo_type(v___y_2425_);
lean_dec_ref(v___y_2425_);
v___x_2433_ = l_Lean_indentExpr(v___x_2432_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_ConstantInfo_type(v___y_2426_);
lean_dec_ref(v___y_2426_);
v___x_2438_ = l_Lean_indentExpr(v___x_2437_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2436_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__11_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_hint_2428_);
v___x_2443_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__1(v___x_2442_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_dec_ref_known(v___x_2443_, 1);
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___y_2424_;
v___y_2407_ = v___y_2423_;
v___y_2408_ = v___y_2427_;
v___y_2409_ = v___y_2429_;
v___y_2410_ = v___y_2430_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___y_2427_);
lean_dec(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
v___jp_2452_:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__15_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___y_2422_ = v___y_2454_;
v___y_2423_ = v___y_2456_;
v___y_2424_ = v___y_2455_;
v___y_2425_ = v___y_2457_;
v___y_2426_ = v___y_2459_;
v___y_2427_ = v___y_2460_;
v_hint_2428_ = v___x_2461_;
v___y_2429_ = v___y_2453_;
v___y_2430_ = v___y_2458_;
goto v___jp_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v___f_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_a_2856_, lean_object* v_declName_2857_, lean_object* v_stx_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v___x_46134__boxed_2862_; lean_object* v_res_2863_; 
v___x_46134__boxed_2862_ = lean_unbox(v___x_2853_);
v_res_2863_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(v___x_2850_, v___x_2851_, v___f_2852_, v___x_46134__boxed_2862_, v___x_2854_, v___x_2855_, v_a_2856_, v_declName_2857_, v_stx_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v_a_2856_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; 
v___x_2883_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2884_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2885_ = 0;
v___f_2886_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2887_ = l_Lean_registerParametricAttributeExt___redArg(v___x_2884_, v___x_2885_, v___f_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___f_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_n(v_a_2888_, 2);
lean_dec_ref_known(v___x_2887_, 1);
v___f_2889_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___f_2890_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2891_ = lean_box(1);
v___x_2892_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_2893_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_));
v___x_2894_ = lean_box(v___x_2885_);
v___f_2895_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed), 12, 7);
lean_closure_set(v___f_2895_, 0, v___x_2883_);
lean_closure_set(v___f_2895_, 1, v___x_2893_);
lean_closure_set(v___f_2895_, 2, v___f_2889_);
lean_closure_set(v___f_2895_, 3, v___x_2894_);
lean_closure_set(v___f_2895_, 4, v___x_2891_);
lean_closure_set(v___f_2895_, 5, v___x_2892_);
lean_closure_set(v___f_2895_, 6, v_a_2888_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_2897_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___f_2895_);
lean_ctor_set(v___x_2897_, 2, v___f_2890_);
lean_ctor_set(v___x_2897_, 3, v___f_2886_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*4, v___x_2885_);
v___x_2898_ = l_Lean_registerParametricAttributeForExt___redArg(v___x_2897_, v_a_2888_);
return v___x_2898_;
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2887_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2887_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2____boxed(lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_();
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2909_, lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___redArg(v_msg_2910_, v___y_2911_, v___y_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2915_, lean_object* v_msg_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__0(v_00_u03b1_2915_, v_msg_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_2921_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__3_spec__8(v_o_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_2931_, lean_object* v_m_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2932_, v_a_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_2935_, lean_object* v_m_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_2935_, v_m_2936_, v_a_2937_);
lean_dec(v_a_2937_);
lean_dec_ref(v_m_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___redArg(v_x_2940_, v_x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_){
_start:
{
uint8_t v_res_2946_; lean_object* v_r_2947_; 
v_res_2946_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_00_u03b2_2943_, v_x_2944_, v_x_2945_);
lean_dec_ref(v_x_2945_);
lean_dec_ref(v_x_2944_);
v_r_2947_ = lean_box(v_res_2946_);
return v_r_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_00_u03b2_2948_, lean_object* v_a_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___redArg(v_a_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2952_, lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_00_u03b2_2952_, v_a_2953_, v_x_2954_);
lean_dec(v_x_2954_);
lean_dec(v_a_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(lean_object* v_00_u03b4_2956_, lean_object* v_t_2957_, lean_object* v_k_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___redArg(v_t_2957_, v_k_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17___boxed(lean_object* v_00_u03b4_2960_, lean_object* v_t_2961_, lean_object* v_k_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__17(v_00_u03b4_2960_, v_t_2961_, v_k_2962_);
lean_dec(v_k_2962_);
lean_dec(v_t_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_2964_, lean_object* v_x_2965_, size_t v_x_2966_, lean_object* v_x_2967_){
_start:
{
uint8_t v___x_2968_; 
v___x_2968_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___redArg(v_x_2965_, v_x_2966_, v_x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_, lean_object* v_x_2972_){
_start:
{
size_t v_x_47415__boxed_2973_; uint8_t v_res_2974_; lean_object* v_r_2975_; 
v_x_47415__boxed_2973_ = lean_unbox_usize(v_x_2971_);
lean_dec(v_x_2971_);
v_res_2974_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12(v_00_u03b2_2969_, v_x_2970_, v_x_47415__boxed_2973_, v_x_2972_);
lean_dec_ref(v_x_2972_);
lean_dec_ref(v_x_2970_);
v_r_2975_ = lean_box(v_res_2974_);
return v_r_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(lean_object* v_givenName_2976_, uint8_t v_skipAuxDecl_2977_, lean_object* v_auxDeclToFullName_2978_, lean_object* v___x_2979_, lean_object* v_givenNameView_2980_, lean_object* v_as_2981_, lean_object* v_i_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___redArg(v_givenName_2976_, v_skipAuxDecl_2977_, v_auxDeclToFullName_2978_, v___x_2979_, v_givenNameView_2980_, v_as_2981_, v_i_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20___boxed(lean_object* v_givenName_2985_, lean_object* v_skipAuxDecl_2986_, lean_object* v_auxDeclToFullName_2987_, lean_object* v___x_2988_, lean_object* v_givenNameView_2989_, lean_object* v_as_2990_, lean_object* v_i_2991_, lean_object* v_a_2992_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2993_; lean_object* v_res_2994_; 
v_skipAuxDecl_boxed_2993_ = lean_unbox(v_skipAuxDecl_2986_);
v_res_2994_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__20(v_givenName_2985_, v_skipAuxDecl_boxed_2993_, v_auxDeclToFullName_2987_, v___x_2988_, v_givenNameView_2989_, v_as_2990_, v_i_2991_, v_a_2992_);
lean_dec_ref(v_as_2990_);
lean_dec(v_auxDeclToFullName_2987_);
lean_dec(v_givenName_2985_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(lean_object* v_localDecl_x3f_2995_, lean_object* v_givenName_2996_, lean_object* v_as_2997_, lean_object* v_i_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___redArg(v_localDecl_x3f_2995_, v_givenName_2996_, v_as_2997_, v_i_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23___boxed(lean_object* v_localDecl_x3f_3001_, lean_object* v_givenName_3002_, lean_object* v_as_3003_, lean_object* v_i_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__23(v_localDecl_x3f_3001_, v_givenName_3002_, v_as_3003_, v_i_3004_, v_a_3005_);
lean_dec_ref(v_as_3003_);
lean_dec(v_givenName_3002_);
lean_dec(v_localDecl_x3f_3001_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(lean_object* v_n_u2080_3007_, lean_object* v_filter_3008_, lean_object* v_view_x3f_3009_, lean_object* v_as_3010_, lean_object* v_as_x27_3011_, lean_object* v_b_3012_, lean_object* v_a_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___redArg(v_n_u2080_3007_, v_filter_3008_, v_view_x3f_3009_, v_as_x27_3011_, v_b_3012_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30___boxed(lean_object* v_n_u2080_3020_, lean_object* v_filter_3021_, lean_object* v_view_x3f_3022_, lean_object* v_as_3023_, lean_object* v_as_x27_3024_, lean_object* v_b_3025_, lean_object* v_a_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__22_spec__30(v_n_u2080_3020_, v_filter_3021_, v_view_x3f_3022_, v_as_3023_, v_as_x27_3024_, v_b_3025_, v_a_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v_as_x27_3024_);
lean_dec(v_as_3023_);
lean_dec(v_n_u2080_3020_);
return v_res_3032_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(lean_object* v_00_u03b2_3033_, lean_object* v_keys_3034_, lean_object* v_vals_3035_, lean_object* v_heq_3036_, lean_object* v_i_3037_, lean_object* v_k_3038_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___redArg(v_keys_3034_, v_i_3037_, v_k_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3040_, lean_object* v_keys_3041_, lean_object* v_vals_3042_, lean_object* v_heq_3043_, lean_object* v_i_3044_, lean_object* v_k_3045_){
_start:
{
uint8_t v_res_3046_; lean_object* v_r_3047_; 
v_res_3046_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4_spec__8_spec__12_spec__17(v_00_u03b2_3040_, v_keys_3041_, v_vals_3042_, v_heq_3043_, v_i_3044_, v_k_3045_);
lean_dec_ref(v_k_3045_);
lean_dec_ref(v_vals_3042_);
lean_dec_ref(v_keys_3041_);
v_r_3047_ = lean_box(v_res_3046_);
return v_r_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(lean_object* v_givenName_3048_, uint8_t v_skipAuxDecl_3049_, lean_object* v_auxDeclToFullName_3050_, lean_object* v___x_3051_, lean_object* v_givenNameView_3052_, lean_object* v_as_3053_, lean_object* v_i_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___redArg(v_givenName_3048_, v_skipAuxDecl_3049_, v_auxDeclToFullName_3050_, v___x_3051_, v_givenNameView_3052_, v_as_3053_, v_i_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24___boxed(lean_object* v_givenName_3057_, lean_object* v_skipAuxDecl_3058_, lean_object* v_auxDeclToFullName_3059_, lean_object* v___x_3060_, lean_object* v_givenNameView_3061_, lean_object* v_as_3062_, lean_object* v_i_3063_, lean_object* v_a_3064_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3065_; lean_object* v_res_3066_; 
v_skipAuxDecl_boxed_3065_ = lean_unbox(v_skipAuxDecl_3058_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__18_spec__21_spec__24(v_givenName_3057_, v_skipAuxDecl_boxed_3065_, v_auxDeclToFullName_3059_, v___x_3060_, v_givenNameView_3061_, v_as_3062_, v_i_3063_, v_a_3064_);
lean_dec_ref(v_as_3062_);
lean_dec(v_auxDeclToFullName_3059_);
lean_dec(v_givenName_3057_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(lean_object* v_localDecl_x3f_3067_, lean_object* v_givenName_3068_, lean_object* v_as_3069_, lean_object* v_i_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___redArg(v_localDecl_x3f_3067_, v_givenName_3068_, v_as_3069_, v_i_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28___boxed(lean_object* v_localDecl_x3f_3073_, lean_object* v_givenName_3074_, lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__19_spec__24_spec__28(v_localDecl_x3f_3073_, v_givenName_3074_, v_as_3075_, v_i_3076_, v_a_3077_);
lean_dec_ref(v_as_3075_);
lean_dec(v_givenName_3074_);
lean_dec(v_localDecl_x3f_3073_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(lean_object* v_opt_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___redArg(v_opt_3079_, v___y_3082_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37___boxed(lean_object* v_opt_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26_spec__32_spec__37(v_opt_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec_ref(v_opt_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(lean_object* v_opt_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___redArg(v_opt_3093_, v___y_3096_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43___boxed(lean_object* v_opt_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__12_spec__25_spec__34_spec__40_spec__43(v_opt_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v_opt_3100_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_3107_, lean_object* v_entry_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_env_3112_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = l_Lean_Linter_deprecatedAttr;
v___x_3114_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_3113_, v_env_3112_, v_declName_3107_, v_entry_3108_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_inst_3111_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 3);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = l_Lean_MessageData_ofFormat(v___x_3120_);
v___x_3122_ = l_Lean_throwError___redArg(v_inst_3109_, v_inst_3110_, v___x_3121_);
return v___x_3122_;
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v_inst_3110_);
lean_dec_ref(v_inst_3109_);
v_a_3125_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3126_ = l_Lean_setEnv___redArg(v_inst_3111_, v_a_3125_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_declName_3130_, lean_object* v_entry_3131_){
_start:
{
lean_object* v_toBind_3132_; lean_object* v_getEnv_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; 
v_toBind_3132_ = lean_ctor_get(v_inst_3127_, 1);
lean_inc(v_toBind_3132_);
v_getEnv_3133_ = lean_ctor_get(v_inst_3128_, 0);
lean_inc(v_getEnv_3133_);
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3134_, 0, v_declName_3130_);
lean_closure_set(v___f_3134_, 1, v_entry_3131_);
lean_closure_set(v___f_3134_, 2, v_inst_3127_);
lean_closure_set(v___f_3134_, 3, v_inst_3129_);
lean_closure_set(v___f_3134_, 4, v_inst_3128_);
v___x_3135_ = lean_apply_4(v_toBind_3132_, lean_box(0), lean_box(0), v_getEnv_3133_, v___f_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_declName_3140_, lean_object* v_entry_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_Linter_setDeprecated___redArg(v_inst_3137_, v_inst_3138_, v_inst_3139_, v_declName_3140_, v_entry_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_3143_, lean_object* v_declName_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3146_ = l_Lean_Linter_deprecatedAttr;
v___x_3147_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3145_, v___x_3146_, v_env_3143_, v_declName_3144_);
if (lean_obj_tag(v___x_3147_) == 0)
{
uint8_t v___x_3148_; 
v___x_3148_ = 0;
return v___x_3148_;
}
else
{
uint8_t v___x_3149_; 
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = 1;
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_3150_, lean_object* v_declName_3151_){
_start:
{
uint8_t v_res_3152_; lean_object* v_r_3153_; 
v_res_3152_ = l_Lean_Linter_isDeprecated(v_env_3150_, v_declName_3151_);
v_r_3153_ = lean_box(v_res_3152_);
return v_r_3153_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_3154_){
_start:
{
lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3156_ = lean_name_eq(v_x_3154_, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_3157_);
lean_dec(v_x_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_3161_){
_start:
{
lean_object* v___f_3162_; uint8_t v___x_3163_; 
v___f_3162_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_3163_ = l_Lean_MessageData_hasTag(v___f_3162_, v_msg_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_3164_){
_start:
{
uint8_t v_res_3165_; lean_object* v_r_3166_; 
v_res_3165_ = l_Lean_MessageData_isDeprecationWarning(v_msg_3164_);
v_r_3166_ = lean_box(v_res_3165_);
return v_r_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_3167_, lean_object* v_declName_3168_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3170_ = l_Lean_Linter_deprecatedAttr;
v___x_3171_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3169_, v___x_3170_, v_env_3167_, v_declName_3168_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_box(0);
return v___x_3172_;
}
else
{
lean_object* v_val_3173_; lean_object* v_newName_x3f_3174_; 
v_val_3173_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_val_3173_);
lean_dec_ref_known(v___x_3171_, 1);
v_newName_x3f_3174_ = lean_ctor_get(v_val_3173_, 0);
lean_inc(v_newName_x3f_3174_);
lean_dec(v_val_3173_);
return v_newName_x3f_3174_;
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 0)
{
if (lean_obj_tag(v_x_3176_) == 0)
{
uint8_t v___x_3177_; 
v___x_3177_ = 1;
return v___x_3177_;
}
else
{
uint8_t v___x_3178_; 
v___x_3178_ = 0;
return v___x_3178_;
}
}
else
{
if (lean_obj_tag(v_x_3176_) == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = 0;
return v___x_3179_;
}
else
{
lean_object* v_head_3180_; lean_object* v_tail_3181_; lean_object* v_head_3182_; lean_object* v_tail_3183_; uint8_t v___x_3184_; 
v_head_3180_ = lean_ctor_get(v_x_3175_, 0);
v_tail_3181_ = lean_ctor_get(v_x_3175_, 1);
v_head_3182_ = lean_ctor_get(v_x_3176_, 0);
v_tail_3183_ = lean_ctor_get(v_x_3176_, 1);
v___x_3184_ = lean_string_dec_eq(v_head_3180_, v_head_3182_);
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
v_x_3175_ = v_tail_3181_;
v_x_3176_ = v_tail_3183_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_3186_, lean_object* v_x_3187_){
_start:
{
uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_res_3188_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_3186_, v_x_3187_);
lean_dec(v_x_3187_);
lean_dec(v_x_3186_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
if (lean_obj_tag(v_x_3191_) == 0)
{
uint8_t v___x_3192_; 
v___x_3192_ = 1;
return v___x_3192_;
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
else
{
if (lean_obj_tag(v_x_3191_) == 0)
{
uint8_t v___x_3194_; 
v___x_3194_ = 0;
return v___x_3194_;
}
else
{
lean_object* v_head_3195_; lean_object* v_tail_3196_; lean_object* v_head_3197_; lean_object* v_tail_3198_; uint8_t v___y_3200_; lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v_fst_3204_; lean_object* v_snd_3205_; uint8_t v___x_3206_; 
v_head_3195_ = lean_ctor_get(v_x_3190_, 0);
v_tail_3196_ = lean_ctor_get(v_x_3190_, 1);
v_head_3197_ = lean_ctor_get(v_x_3191_, 0);
v_tail_3198_ = lean_ctor_get(v_x_3191_, 1);
v_fst_3202_ = lean_ctor_get(v_head_3195_, 0);
v_snd_3203_ = lean_ctor_get(v_head_3195_, 1);
v_fst_3204_ = lean_ctor_get(v_head_3197_, 0);
v_snd_3205_ = lean_ctor_get(v_head_3197_, 1);
v___x_3206_ = lean_name_eq(v_fst_3202_, v_fst_3204_);
if (v___x_3206_ == 0)
{
v___y_3200_ = v___x_3206_;
goto v___jp_3199_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_snd_3203_, v_snd_3205_);
v___y_3200_ = v___x_3207_;
goto v___jp_3199_;
}
v___jp_3199_:
{
if (v___y_3200_ == 0)
{
return v___y_3200_;
}
else
{
v_x_3190_ = v_tail_3196_;
v_x_3191_ = v_tail_3198_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_x_3208_, v_x_3209_);
lean_dec(v_x_3209_);
lean_dec(v_x_3208_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_3214_ = l_Lean_stringToMessageData(v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_3215_, lean_object* v_newName_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_ref_3222_; 
v_ref_3222_ = lean_ctor_get(v_a_3219_, 5);
if (lean_obj_tag(v_ref_3222_) == 3)
{
lean_object* v_val_3223_; uint8_t v___x_3224_; 
v_val_3223_ = lean_ctor_get(v_ref_3222_, 2);
v___x_3224_ = l_Lean_Name_hasMacroScopes(v_val_3223_);
if (v___x_3224_ == 0)
{
uint8_t v___x_3225_; lean_object* v___x_3303_; 
v___x_3225_ = 1;
v___x_3303_ = l_Lean_Syntax_getRange_x3f(v_ref_3222_, v___x_3225_);
if (lean_obj_tag(v___x_3303_) == 0)
{
if (v___x_3224_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v_newName_3216_);
lean_dec(v_declName_3215_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
else
{
goto v___jp_3226_;
}
}
else
{
lean_dec_ref_known(v___x_3303_, 1);
goto v___jp_3226_;
}
v___jp_3226_:
{
lean_object* v___x_3227_; 
lean_inc(v_val_3223_);
v___x_3227_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5_spec__11_spec__20_spec__26(v_val_3223_, v___x_3225_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3294_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3294_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3294_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3232_ = lean_box(0);
v___x_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_declName_3215_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
v___x_3235_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_a_3228_, v___x_3234_);
lean_dec_ref_known(v___x_3234_, 2);
lean_dec(v_a_3228_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_dec(v_newName_3216_);
v___x_3236_ = lean_box(0);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3236_);
v___x_3238_ = v___x_3230_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
else
{
lean_object* v___x_3240_; 
lean_del_object(v___x_3230_);
v___x_3240_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__5(v_newName_3216_, v___x_3224_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3285_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3285_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3285_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
if (lean_obj_tag(v_a_3241_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3280_; 
lean_del_object(v___x_3243_);
v_val_3245_ = lean_ctor_get(v_a_3241_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_a_3241_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3247_ = v_a_3241_;
v_isShared_3248_ = v_isSharedCheck_3280_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_val_3245_);
lean_dec(v_a_3241_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3280_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3249_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_3250_ = l_Lean_Name_toString(v_val_3245_, v___x_3225_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
lean_ctor_set(v___x_3253_, 2, v___x_3252_);
lean_ctor_set(v___x_3253_, 3, v___x_3252_);
lean_ctor_set(v___x_3253_, 4, v___x_3252_);
lean_ctor_set(v___x_3253_, 5, v___x_3252_);
v___x_3254_ = 0;
v___x_3255_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3252_);
lean_ctor_set(v___x_3255_, 2, v___x_3252_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*3, v___x_3254_);
v___x_3256_ = lean_unsigned_to_nat(1u);
v___x_3257_ = lean_mk_empty_array_with_capacity(v___x_3256_);
v___x_3258_ = lean_array_push(v___x_3257_, v___x_3255_);
lean_inc_ref(v_ref_3222_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v_ref_3222_);
v___x_3260_ = v___x_3247_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_ref_3222_);
v___x_3260_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_MessageData_hint(v___x_3249_, v___x_3258_, v___x_3260_, v___x_3252_, v___x_3224_, v_a_3219_, v_a_3220_);
lean_dec_ref(v___x_3258_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3270_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3270_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_a_3262_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3268_ = v___x_3264_;
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
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
v_a_3271_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3261_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3261_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_a_3241_);
v___x_3281_ = lean_box(0);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3281_);
v___x_3283_ = v___x_3243_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3240_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3240_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_newName_3216_);
lean_dec(v_declName_3215_);
v_a_3295_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3227_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3227_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_newName_3216_);
lean_dec(v_declName_3215_);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_newName_3216_);
lean_dec(v_declName_3215_);
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3310_, lean_object* v_newName_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3310_, v_newName_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v_env_3322_; lean_object* v___x_3323_; lean_object* v_toEnvExtension_3324_; lean_object* v_asyncMode_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v_merged_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v___x_3321_ = lean_st_ref_get(v___y_3319_);
v_env_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc_ref(v_env_3322_);
lean_dec(v___x_3321_);
v___x_3323_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3324_ = lean_ctor_get(v___x_3323_, 0);
v_asyncMode_3325_ = lean_ctor_get(v_toEnvExtension_3324_, 2);
v___x_3326_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3327_ = lean_box(0);
v___x_3328_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3326_, v___x_3323_, v_env_3322_, v_asyncMode_3325_, v___x_3327_);
v_merged_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3328_, 1);
lean_dec(v_unused_3338_);
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_merged_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v_merged_3329_);
lean_ctor_set(v___x_3331_, 0, v_o_3318_);
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_o_3318_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_merged_3329_);
v___x_3334_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3339_, v___y_3340_);
lean_dec(v___y_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_options_3348_; lean_object* v___x_3349_; 
v_options_3348_ = lean_ctor_get(v___y_3345_, 2);
lean_inc_ref(v_options_3348_);
v___x_3349_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_3348_, v___y_3346_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3355_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
return v___x_3367_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3380_ = l_Lean_MessageData_ofFormat(v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3383_ = l_Lean_stringToMessageData(v___x_3382_);
return v___x_3383_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3389_ = l_Lean_stringToMessageData(v___x_3388_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3392_ = l_Lean_stringToMessageData(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3399_, uint8_t v_allowSuggestion_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3579_; 
v___x_3406_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3579_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3579_;
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
lean_dec(v_declName_3399_);
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
lean_object* v___x_3432_; lean_object* v_env_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3432_ = lean_st_ref_get(v_a_3404_);
v_env_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc_ref(v_env_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3435_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3399_);
v___x_3436_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3434_, v___x_3435_, v_env_3433_, v_declName_3399_);
if (lean_obj_tag(v___x_3436_) == 1)
{
lean_object* v_val_3437_; lean_object* v_text_x3f_3438_; 
lean_del_object(v___x_3409_);
v_val_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_val_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v_text_x3f_3438_ = lean_ctor_get(v_val_3437_, 1);
if (lean_obj_tag(v_text_x3f_3438_) == 0)
{
lean_object* v_newName_x3f_3439_; 
v_newName_x3f_3439_ = lean_ctor_get(v_val_3437_, 0);
lean_inc(v_newName_x3f_3439_);
lean_dec(v_val_3437_);
if (lean_obj_tag(v_newName_x3f_3439_) == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_3414_ = v___x_3440_;
v___y_3415_ = v_a_3401_;
v___y_3416_ = v_a_3402_;
v___y_3417_ = v_a_3403_;
v___y_3418_ = v_a_3404_;
goto v___jp_3413_;
}
else
{
lean_object* v_val_3441_; lean_object* v___x_3442_; lean_object* v_env_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3451_; 
v_val_3441_ = lean_ctor_get(v_newName_x3f_3439_, 0);
lean_inc_n(v_val_3441_, 2);
lean_dec_ref_known(v_newName_x3f_3439_, 1);
v___x_3442_ = lean_st_ref_get(v_a_3404_);
v_env_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc_ref_n(v_env_3443_, 2);
lean_dec(v___x_3442_);
v___x_3444_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3445_ = l_Lean_MessageData_ofConstName(v_val_3441_, v___x_3412_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__58_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Lean_Name_getPrefix(v_declName_3399_);
v___x_3450_ = 0;
lean_inc(v_declName_3399_);
v___x_3451_ = l_Lean_Environment_find_x3f(v_env_3443_, v_declName_3399_, v___x_3450_);
if (lean_obj_tag(v___x_3451_) == 1)
{
lean_object* v_val_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_val_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_val_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = l_Lean_Name_getPrefix(v_val_3441_);
lean_inc(v_val_3441_);
lean_inc_ref(v_env_3443_);
v___x_3454_ = l_Lean_Environment_find_x3f(v_env_3443_, v_val_3441_, v___x_3450_);
if (lean_obj_tag(v___x_3454_) == 1)
{
lean_object* v_val_3455_; lean_object* v___x_3456_; 
v_val_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3452_, v_val_3455_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v_msg_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v_msg_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; uint8_t v___x_3551_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3551_ = lean_unbox(v_a_3457_);
if (v___x_3551_ == 0)
{
if (v___x_3412_ == 0)
{
lean_dec(v_val_3455_);
lean_dec(v_val_3452_);
v_msg_3544_ = v___x_3448_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
v___y_3548_ = v_a_3404_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3552_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__7_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3553_ = l_Lean_ConstantInfo_type(v_val_3455_);
lean_dec(v_val_3455_);
v___x_3554_ = l_Lean_indentExpr(v___x_3553_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3552_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__9_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_ConstantInfo_type(v_val_3452_);
lean_dec(v_val_3452_);
v___x_3559_ = l_Lean_indentExpr(v___x_3558_);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3557_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_MessageData_note(v___x_3560_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3448_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v_msg_3544_ = v___x_3562_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
v___y_3548_ = v_a_3404_;
goto v___jp_3543_;
}
}
else
{
lean_dec(v_val_3455_);
lean_dec(v_val_3452_);
v_msg_3544_ = v___x_3448_;
v___y_3545_ = v_a_3401_;
v___y_3546_ = v_a_3402_;
v___y_3547_ = v_a_3403_;
v___y_3548_ = v_a_3404_;
goto v___jp_3543_;
}
v___jp_3458_:
{
if (v_allowSuggestion_3400_ == 0)
{
lean_dec(v_a_3457_);
lean_dec(v_val_3441_);
v_extraMsg_3414_ = v_msg_3459_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3461_;
v___y_3417_ = v___y_3462_;
v___y_3418_ = v___y_3463_;
goto v___jp_3413_;
}
else
{
uint8_t v___x_3464_; 
v___x_3464_ = lean_unbox(v_a_3457_);
lean_dec(v_a_3457_);
if (v___x_3464_ == 0)
{
lean_dec(v_val_3441_);
v_extraMsg_3414_ = v_msg_3459_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3461_;
v___y_3417_ = v___y_3462_;
v___y_3418_ = v___y_3463_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3465_; 
lean_inc(v_declName_3399_);
v___x_3465_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3399_, v_val_3441_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
if (lean_obj_tag(v_a_3466_) == 1)
{
lean_object* v_val_3467_; lean_object* v___x_3468_; 
v_val_3467_ = lean_ctor_get(v_a_3466_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_a_3466_, 1);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_msg_3459_);
lean_ctor_set(v___x_3468_, 1, v_val_3467_);
v_extraMsg_3414_ = v___x_3468_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3461_;
v___y_3417_ = v___y_3462_;
v___y_3418_ = v___y_3463_;
goto v___jp_3413_;
}
else
{
lean_dec(v_a_3466_);
v_extraMsg_3414_ = v_msg_3459_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3461_;
v___y_3417_ = v___y_3462_;
v___y_3418_ = v___y_3463_;
goto v___jp_3413_;
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v_msg_3459_);
lean_dec(v_declName_3399_);
v_a_3469_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3465_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3465_);
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
}
}
v___jp_3477_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3484_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___x_3445_);
v___x_3486_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___y_3483_);
v___x_3489_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = l_Lean_MessageData_ofName(v___x_3453_);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_MessageData_note(v___x_3494_);
v___x_3496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___y_3479_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v_msg_3459_ = v___x_3496_;
v___y_3460_ = v___y_3480_;
v___y_3461_ = v___y_3478_;
v___y_3462_ = v___y_3482_;
v___y_3463_ = v___y_3481_;
goto v___jp_3458_;
}
v___jp_3497_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3504_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___y_3503_);
v___x_3506_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_MessageData_note(v___x_3507_);
v___x_3509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___y_3499_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v_msg_3459_ = v___x_3509_;
v___y_3460_ = v___y_3500_;
v___y_3461_ = v___y_3498_;
v___y_3462_ = v___y_3502_;
v___y_3463_ = v___y_3501_;
goto v___jp_3458_;
}
v___jp_3510_:
{
if (v___y_3517_ == 0)
{
uint8_t v___x_3518_; 
lean_inc(v_declName_3399_);
lean_inc_ref(v_env_3443_);
v___x_3518_ = l_Lean_isProtected(v_env_3443_, v_declName_3399_);
if (v___x_3518_ == 0)
{
if (v___x_3412_ == 0)
{
lean_dec(v___x_3453_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
v_msg_3459_ = v___y_3512_;
v___y_3460_ = v___y_3514_;
v___y_3461_ = v___y_3511_;
v___y_3462_ = v___y_3516_;
v___y_3463_ = v___y_3515_;
goto v___jp_3458_;
}
else
{
uint8_t v___x_3519_; 
lean_inc(v_val_3441_);
v___x_3519_ = l_Lean_isProtected(v_env_3443_, v_val_3441_);
if (v___x_3519_ == 0)
{
lean_dec(v___x_3453_);
lean_dec_ref(v___x_3445_);
v_msg_3459_ = v___y_3512_;
v___y_3460_ = v___y_3514_;
v___y_3461_ = v___y_3511_;
v___y_3462_ = v___y_3516_;
v___y_3463_ = v___y_3515_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
lean_inc(v___x_3453_);
v___x_3520_ = l_Lean_Name_componentsRev(v___x_3453_);
v___x_3521_ = lean_unsigned_to_nat(1u);
v___x_3522_ = l_List_lengthTR___redArg(v___x_3520_);
v___x_3523_ = lean_nat_dec_lt(v___x_3521_, v___x_3522_);
lean_dec(v___x_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v___x_3520_);
v___x_3524_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___y_3478_ = v___y_3511_;
v___y_3479_ = v___y_3512_;
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3515_;
v___y_3482_ = v___y_3516_;
v___y_3483_ = v___x_3524_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3525_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = l_List_get___redArg(v___x_3520_, v___x_3526_);
lean_dec(v___x_3520_);
v___x_3528_ = l_Lean_MessageData_ofName(v___x_3527_);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3525_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___y_3478_ = v___y_3511_;
v___y_3479_ = v___y_3512_;
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3515_;
v___y_3482_ = v___y_3516_;
v___y_3483_ = v___x_3531_;
goto v___jp_3477_;
}
}
}
}
else
{
lean_dec(v___x_3453_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
v_msg_3459_ = v___y_3512_;
v___y_3460_ = v___y_3514_;
v___y_3461_ = v___y_3511_;
v___y_3462_ = v___y_3516_;
v___y_3463_ = v___y_3515_;
goto v___jp_3458_;
}
}
else
{
lean_dec(v___x_3453_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
if (lean_obj_tag(v_declName_3399_) == 1)
{
lean_object* v_str_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_str_3532_ = lean_ctor_get(v_declName_3399_, 1);
v___x_3533_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
lean_inc_ref(v_str_3532_);
v___x_3534_ = l_Lean_stringToMessageData(v_str_3532_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
lean_inc(v_val_3441_);
v___x_3538_ = l_Lean_MessageData_ofConstName(v_val_3441_, v___y_3513_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3516_;
v___y_3503_ = v___x_3541_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_MessageData_nil;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3516_;
v___y_3503_ = v___x_3542_;
goto v___jp_3497_;
}
}
}
v___jp_3543_:
{
uint8_t v___x_3549_; 
v___x_3549_ = l_Lean_Name_isAnonymous(v___x_3449_);
if (v___x_3549_ == 0)
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_name_eq(v___x_3449_, v___x_3453_);
lean_dec(v___x_3449_);
if (v___x_3550_ == 0)
{
v___y_3511_ = v___y_3546_;
v___y_3512_ = v_msg_3544_;
v___y_3513_ = v___x_3549_;
v___y_3514_ = v___y_3545_;
v___y_3515_ = v___y_3548_;
v___y_3516_ = v___y_3547_;
v___y_3517_ = v___x_3412_;
goto v___jp_3510_;
}
else
{
v___y_3511_ = v___y_3546_;
v___y_3512_ = v_msg_3544_;
v___y_3513_ = v___x_3549_;
v___y_3514_ = v___y_3545_;
v___y_3515_ = v___y_3548_;
v___y_3516_ = v___y_3547_;
v___y_3517_ = v___x_3549_;
goto v___jp_3510_;
}
}
else
{
lean_dec(v___x_3453_);
lean_dec(v___x_3449_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
v_msg_3459_ = v_msg_3544_;
v___y_3460_ = v___y_3545_;
v___y_3461_ = v___y_3546_;
v___y_3462_ = v___y_3547_;
v___y_3463_ = v___y_3548_;
goto v___jp_3458_;
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_val_3455_);
lean_dec(v___x_3453_);
lean_dec(v_val_3452_);
lean_dec(v___x_3449_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
lean_dec(v_val_3441_);
lean_dec(v_declName_3399_);
v_a_3563_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3456_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3456_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_dec(v___x_3454_);
lean_dec(v___x_3453_);
lean_dec(v_val_3452_);
lean_dec(v___x_3449_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
lean_dec(v_val_3441_);
v_extraMsg_3414_ = v___x_3448_;
v___y_3415_ = v_a_3401_;
v___y_3416_ = v_a_3402_;
v___y_3417_ = v_a_3403_;
v___y_3418_ = v_a_3404_;
goto v___jp_3413_;
}
}
else
{
lean_dec(v___x_3451_);
lean_dec(v___x_3449_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3443_);
lean_dec(v_val_3441_);
v_extraMsg_3414_ = v___x_3448_;
v___y_3415_ = v_a_3401_;
v___y_3416_ = v_a_3402_;
v___y_3417_ = v_a_3403_;
v___y_3418_ = v_a_3404_;
goto v___jp_3413_;
}
}
}
else
{
lean_object* v_val_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_inc_ref(v_text_x3f_3438_);
lean_dec(v_val_3437_);
v_val_3571_ = lean_ctor_get(v_text_x3f_3438_, 0);
lean_inc(v_val_3571_);
lean_dec_ref_known(v_text_x3f_3438_, 1);
v___x_3572_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3573_ = l_Lean_stringToMessageData(v_val_3571_);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v_extraMsg_3414_ = v___x_3574_;
v___y_3415_ = v_a_3401_;
v___y_3416_ = v_a_3402_;
v___y_3417_ = v_a_3403_;
v___y_3418_ = v_a_3404_;
goto v___jp_3413_;
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
lean_dec(v___x_3436_);
lean_dec(v_declName_3399_);
v___x_3575_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3575_);
v___x_3577_ = v___x_3409_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
v___jp_3413_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_));
v___x_3420_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3___closed__46_00___x40_Lean_Linter_Deprecated_1425340232____hygCtx___hyg_2_);
v___x_3421_ = l_Lean_MessageData_ofConstName(v_declName_3399_, v___x_3412_);
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3580_, lean_object* v_allowSuggestion_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
uint8_t v_allowSuggestion_boxed_3587_; lean_object* v_res_3588_; 
v_allowSuggestion_boxed_3587_ = lean_unbox(v_allowSuggestion_3581_);
v_res_3588_ = l_Lean_Linter_checkDeprecated(v_declName_3580_, v_allowSuggestion_boxed_3587_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3589_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
return v_res_3602_;
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
