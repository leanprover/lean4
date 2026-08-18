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
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 372, .m_capacity = 372, .m_length = 371, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often expected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__0 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__1;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__2 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__2_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__3;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": Use `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__4 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__5;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__6 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__7;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` is protected. References to this constant must include "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__8 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__9;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "its prefix `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__10 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__11;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` even when inside its namespace."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__12 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__13;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "The updated constant is in a different namespace. Dot notation may need to be changed"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__14 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__15;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__16 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__17;
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value)}};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__18 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__18_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__19;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "at least the last component `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__20 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__20_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__21;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "` of "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__22 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__22_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__23;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " (e.g., from `x."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__24 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__24_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__25;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__26 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__26_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__27;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " x`)"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__28 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__28_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__29;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__30 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__30_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__31;
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
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
if (lean_obj_tag(v_a_66_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_array_to_list(v_a_67_);
return v___x_68_;
}
else
{
lean_object* v_tail_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_tail_69_ = lean_ctor_get(v_a_66_, 1);
v___x_70_ = lean_array_get_size(v_a_67_);
v___x_71_ = ((lean_object*)(l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___closed__1));
v___x_72_ = l_Lean_Name_num___override(v___x_71_, v___x_70_);
v___x_73_ = l_Lean_mkLevelParam(v___x_72_);
v___x_74_ = lean_array_push(v_a_67_, v___x_73_);
v_a_66_ = v_tail_69_;
v_a_67_ = v___x_74_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0___boxed(lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v_a_76_, v_a_77_);
lean_dec(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(lean_object* v_decl_u2081_81_, lean_object* v_decl_u2082_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_88_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2081_81_);
v___x_89_ = l_Lean_ConstantInfo_numLevelParams(v_decl_u2082_82_);
v___x_90_ = lean_nat_dec_eq(v___x_88_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_88_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_keyedConfig_93_; uint8_t v_trackZetaDelta_94_; lean_object* v_zetaDeltaSet_95_; lean_object* v_lctx_96_; lean_object* v_localInstances_97_; lean_object* v_defEqCtx_x3f_98_; lean_object* v_synthPendingDepth_99_; lean_object* v_customCanUnfoldPredicate_x3f_100_; uint8_t v_univApprox_101_; uint8_t v_inTypeClassResolution_102_; uint8_t v_cacheInferType_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_levels_106_; lean_object* v_type_u2081_107_; lean_object* v_type_u2082_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_keyedConfig_93_ = lean_ctor_get(v_a_83_, 0);
v_trackZetaDelta_94_ = lean_ctor_get_uint8(v_a_83_, sizeof(void*)*7);
v_zetaDeltaSet_95_ = lean_ctor_get(v_a_83_, 1);
v_lctx_96_ = lean_ctor_get(v_a_83_, 2);
v_localInstances_97_ = lean_ctor_get(v_a_83_, 3);
v_defEqCtx_x3f_98_ = lean_ctor_get(v_a_83_, 4);
v_synthPendingDepth_99_ = lean_ctor_get(v_a_83_, 5);
v_customCanUnfoldPredicate_x3f_100_ = lean_ctor_get(v_a_83_, 6);
v_univApprox_101_ = lean_ctor_get_uint8(v_a_83_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_102_ = lean_ctor_get_uint8(v_a_83_, sizeof(void*)*7 + 2);
v_cacheInferType_103_ = lean_ctor_get_uint8(v_a_83_, sizeof(void*)*7 + 3);
v___x_104_ = l_Lean_ConstantInfo_levelParams(v_decl_u2081_81_);
v___x_105_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___closed__0));
v_levels_106_ = l_List_mapIdx_go___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq_spec__0(v___x_104_, v___x_105_);
lean_dec(v___x_104_);
lean_inc(v_levels_106_);
v_type_u2081_107_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2081_81_, v_levels_106_);
v_type_u2082_108_ = l_Lean_ConstantInfo_instantiateTypeLevelParams(v_decl_u2082_82_, v_levels_106_);
v___x_109_ = 2;
lean_inc_ref(v_keyedConfig_93_);
v___x_110_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_109_, v_keyedConfig_93_);
lean_inc(v_customCanUnfoldPredicate_x3f_100_);
lean_inc(v_synthPendingDepth_99_);
lean_inc(v_defEqCtx_x3f_98_);
lean_inc_ref(v_localInstances_97_);
lean_inc_ref(v_lctx_96_);
lean_inc(v_zetaDeltaSet_95_);
v___x_111_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_zetaDeltaSet_95_);
lean_ctor_set(v___x_111_, 2, v_lctx_96_);
lean_ctor_set(v___x_111_, 3, v_localInstances_97_);
lean_ctor_set(v___x_111_, 4, v_defEqCtx_x3f_98_);
lean_ctor_set(v___x_111_, 5, v_synthPendingDepth_99_);
lean_ctor_set(v___x_111_, 6, v_customCanUnfoldPredicate_x3f_100_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7, v_trackZetaDelta_94_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 1, v_univApprox_101_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 2, v_inTypeClassResolution_102_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 3, v_cacheInferType_103_);
v___x_112_ = l_Lean_Meta_isExprDefEqGuarded(v_type_u2081_107_, v_type_u2082_108_, v___x_111_, v_a_84_, v_a_85_, v_a_86_);
lean_dec_ref_known(v___x_111_, 7);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq___boxed(lean_object* v_decl_u2081_113_, lean_object* v_decl_u2082_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_decl_u2081_113_, v_decl_u2082_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec_ref(v_decl_u2082_114_);
lean_dec_ref(v_decl_u2081_113_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
else
{
if (lean_obj_tag(v_x_122_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v_val_127_; uint8_t v___x_128_; 
v_val_126_ = lean_ctor_get(v_x_121_, 0);
v_val_127_ = lean_ctor_get(v_x_122_, 0);
v___x_128_ = lean_name_eq(v_val_126_, v_val_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v_x_136_);
lean_dec_ref(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v_x_145_, v_x_146_, v_x_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v_x_147_);
lean_dec_ref(v_x_146_);
lean_dec(v_x_145_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t v___y_159_, uint8_t v_suppressElabErrors_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 1)
{
lean_object* v_pre_162_; 
v_pre_162_ = lean_ctor_get(v_x_161_, 0);
switch(lean_obj_tag(v_pre_162_))
{
case 1:
{
lean_object* v_pre_163_; 
v_pre_163_ = lean_ctor_get(v_pre_162_, 0);
switch(lean_obj_tag(v_pre_163_))
{
case 0:
{
lean_object* v_str_164_; lean_object* v_str_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_str_164_ = lean_ctor_get(v_x_161_, 1);
v_str_165_ = lean_ctor_get(v_pre_162_, 1);
v___x_166_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0));
v___x_167_ = lean_string_dec_eq(v_str_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1));
v___x_169_ = lean_string_dec_eq(v_str_165_, v___x_168_);
if (v___x_169_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2));
v___x_171_ = lean_string_dec_eq(v_str_164_, v___x_170_);
if (v___x_171_ == 0)
{
return v___y_159_;
}
else
{
return v_suppressElabErrors_160_;
}
}
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3));
v___x_173_ = lean_string_dec_eq(v_str_164_, v___x_172_);
if (v___x_173_ == 0)
{
return v___y_159_;
}
else
{
return v_suppressElabErrors_160_;
}
}
}
case 1:
{
lean_object* v_pre_174_; 
v_pre_174_ = lean_ctor_get(v_pre_163_, 0);
if (lean_obj_tag(v_pre_174_) == 0)
{
lean_object* v_str_175_; lean_object* v_str_176_; lean_object* v_str_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_str_175_ = lean_ctor_get(v_x_161_, 1);
v_str_176_ = lean_ctor_get(v_pre_162_, 1);
v_str_177_ = lean_ctor_get(v_pre_163_, 1);
v___x_178_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4));
v___x_179_ = lean_string_dec_eq(v_str_177_, v___x_178_);
if (v___x_179_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5));
v___x_181_ = lean_string_dec_eq(v_str_176_, v___x_180_);
if (v___x_181_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6));
v___x_183_ = lean_string_dec_eq(v_str_175_, v___x_182_);
if (v___x_183_ == 0)
{
return v___y_159_;
}
else
{
return v_suppressElabErrors_160_;
}
}
}
}
else
{
return v___y_159_;
}
}
default: 
{
return v___y_159_;
}
}
}
case 0:
{
lean_object* v_str_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_str_184_ = lean_ctor_get(v_x_161_, 1);
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7));
v___x_186_ = lean_string_dec_eq(v_str_184_, v___x_185_);
if (v___x_186_ == 0)
{
return v___y_159_;
}
else
{
return v_suppressElabErrors_160_;
}
}
default: 
{
return v___y_159_;
}
}
}
else
{
return v___y_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___y_187_, lean_object* v_suppressElabErrors_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___y_16065__boxed_190_; uint8_t v_suppressElabErrors_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v___y_16065__boxed_190_ = lean_unbox(v___y_187_);
v_suppressElabErrors_boxed_191_ = lean_unbox(v_suppressElabErrors_188_);
v_res_192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_16065__boxed_190_, v_suppressElabErrors_boxed_191_, v_x_189_);
lean_dec(v_x_189_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_opts_194_, lean_object* v_opt_195_){
_start:
{
lean_object* v_name_196_; lean_object* v_defValue_197_; lean_object* v_map_198_; lean_object* v___x_199_; 
v_name_196_ = lean_ctor_get(v_opt_195_, 0);
v_defValue_197_ = lean_ctor_get(v_opt_195_, 1);
v_map_198_ = lean_ctor_get(v_opts_194_, 0);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_198_, v_name_196_);
if (lean_obj_tag(v___x_199_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_defValue_197_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_199_, 1);
if (lean_obj_tag(v_val_201_) == 1)
{
uint8_t v_v_202_; 
v_v_202_ = lean_ctor_get_uint8(v_val_201_, 0);
lean_dec_ref_known(v_val_201_, 0);
return v_v_202_;
}
else
{
uint8_t v___x_203_; 
lean_dec(v_val_201_);
v___x_203_ = lean_unbox(v_defValue_197_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_204_, lean_object* v_opt_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_opts_204_, v_opt_205_);
lean_dec_ref(v_opt_205_);
lean_dec_ref(v_opts_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
lean_ctor_set(v___x_213_, 3, v___x_212_);
lean_ctor_set(v___x_213_, 4, v___x_211_);
lean_ctor_set(v___x_213_, 5, v___x_211_);
lean_ctor_set(v___x_213_, 6, v___x_211_);
lean_ctor_set(v___x_213_, 7, v___x_211_);
lean_ctor_set(v___x_213_, 8, v___x_211_);
lean_ctor_set(v___x_213_, 9, v___x_211_);
lean_ctor_set(v___x_213_, 10, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(32u);
v___x_215_ = lean_mk_empty_array_with_capacity(v___x_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = ((size_t)5ULL);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_unsigned_to_nat(32u);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_222_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_218_);
lean_ctor_set(v___x_222_, 3, v___x_218_);
lean_ctor_set_usize(v___x_222_, 4, v___x_217_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_box(1);
v___x_224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_231_ = lean_st_ref_get(v___y_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v_options_233_ = lean_ctor_get(v___y_228_, 2);
v___x_234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_233_);
v___x_236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_236_, 0, v_env_232_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set(v___x_236_, 3, v_options_233_);
v___x_237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_msgData_227_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(v_msgData_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_ref_245_, lean_object* v_msgData_246_, uint8_t v_severity_247_, uint8_t v_isSilent_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; uint8_t v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___y_294_; uint8_t v___y_295_; lean_object* v___y_296_; lean_object* v___y_314_; uint8_t v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; uint8_t v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; uint8_t v___x_336_; lean_object* v___y_338_; lean_object* v___y_339_; uint8_t v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; uint8_t v___y_344_; uint8_t v___y_346_; uint8_t v___x_361_; 
v___x_336_ = 2;
v___x_361_ = l_Lean_instBEqMessageSeverity_beq(v_severity_247_, v___x_336_);
if (v___x_361_ == 0)
{
v___y_346_ = v___x_361_;
goto v___jp_345_;
}
else
{
uint8_t v___x_362_; 
lean_inc_ref(v_msgData_246_);
v___x_362_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_246_);
v___y_346_ = v___x_362_;
goto v___jp_345_;
}
v___jp_252_:
{
lean_object* v___x_262_; lean_object* v_currNamespace_263_; lean_object* v_openDecls_264_; lean_object* v_env_265_; lean_object* v_nextMacroScope_266_; lean_object* v_ngen_267_; lean_object* v_auxDeclNGen_268_; lean_object* v_traceState_269_; lean_object* v_cache_270_; lean_object* v_messages_271_; lean_object* v_infoState_272_; lean_object* v_snapshotTasks_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_287_; 
v___x_262_ = lean_st_ref_take(v___y_261_);
v_currNamespace_263_ = lean_ctor_get(v___y_260_, 6);
v_openDecls_264_ = lean_ctor_get(v___y_260_, 7);
v_env_265_ = lean_ctor_get(v___x_262_, 0);
v_nextMacroScope_266_ = lean_ctor_get(v___x_262_, 1);
v_ngen_267_ = lean_ctor_get(v___x_262_, 2);
v_auxDeclNGen_268_ = lean_ctor_get(v___x_262_, 3);
v_traceState_269_ = lean_ctor_get(v___x_262_, 4);
v_cache_270_ = lean_ctor_get(v___x_262_, 5);
v_messages_271_ = lean_ctor_get(v___x_262_, 6);
v_infoState_272_ = lean_ctor_get(v___x_262_, 7);
v_snapshotTasks_273_ = lean_ctor_get(v___x_262_, 8);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_287_ == 0)
{
v___x_275_ = v___x_262_;
v_isShared_276_ = v_isSharedCheck_287_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snapshotTasks_273_);
lean_inc(v_infoState_272_);
lean_inc(v_messages_271_);
lean_inc(v_cache_270_);
lean_inc(v_traceState_269_);
lean_inc(v_auxDeclNGen_268_);
lean_inc(v_ngen_267_);
lean_inc(v_nextMacroScope_266_);
lean_inc(v_env_265_);
lean_dec(v___x_262_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_287_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_inc(v_openDecls_264_);
lean_inc(v_currNamespace_263_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_currNamespace_263_);
lean_ctor_set(v___x_277_, 1, v_openDecls_264_);
v___x_278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___y_255_);
lean_inc_ref(v___y_253_);
lean_inc_ref(v___y_256_);
v___x_279_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_279_, 0, v___y_256_);
lean_ctor_set(v___x_279_, 1, v___y_258_);
lean_ctor_set(v___x_279_, 2, v___y_257_);
lean_ctor_set(v___x_279_, 3, v___y_253_);
lean_ctor_set(v___x_279_, 4, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5, v___y_259_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5 + 1, v___y_254_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5 + 2, v_isSilent_248_);
v___x_280_ = l_Lean_MessageLog_add(v___x_279_, v_messages_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 6, v___x_280_);
v___x_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_env_265_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_nextMacroScope_266_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_ngen_267_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_auxDeclNGen_268_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_traceState_269_);
lean_ctor_set(v_reuseFailAlloc_286_, 5, v_cache_270_);
lean_ctor_set(v_reuseFailAlloc_286_, 6, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 7, v_infoState_272_);
lean_ctor_set(v_reuseFailAlloc_286_, 8, v_snapshotTasks_273_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_st_ref_put(v___y_261_, v___x_282_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
v___jp_288_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_312_; 
v___x_297_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_246_);
v___x_298_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(v___x_297_, v___y_249_, v___y_250_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_312_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_312_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_312_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc_ref_n(v___y_292_, 2);
v___x_303_ = l_Lean_FileMap_toPosition(v___y_292_, v___y_291_);
lean_dec(v___y_291_);
v___x_304_ = l_Lean_FileMap_toPosition(v___y_292_, v___y_296_);
lean_dec(v___y_296_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_295_ == 0)
{
lean_del_object(v___x_301_);
lean_dec_ref(v___y_289_);
v___y_253_ = v___x_306_;
v___y_254_ = v___y_290_;
v___y_255_ = v_a_299_;
v___y_256_ = v___y_293_;
v___y_257_ = v___x_305_;
v___y_258_ = v___x_303_;
v___y_259_ = v___y_294_;
v___y_260_ = v___y_249_;
v___y_261_ = v___y_250_;
goto v___jp_252_;
}
else
{
uint8_t v___x_307_; 
lean_inc(v_a_299_);
v___x_307_ = l_Lean_MessageData_hasTag(v___y_289_, v_a_299_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec_ref_known(v___x_305_, 1);
lean_dec_ref(v___x_303_);
lean_dec(v_a_299_);
v___x_308_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_308_);
v___x_310_ = v___x_301_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
lean_del_object(v___x_301_);
v___y_253_ = v___x_306_;
v___y_254_ = v___y_290_;
v___y_255_ = v_a_299_;
v___y_256_ = v___y_293_;
v___y_257_ = v___x_305_;
v___y_258_ = v___x_303_;
v___y_259_ = v___y_294_;
v___y_260_ = v___y_249_;
v___y_261_ = v___y_250_;
goto v___jp_252_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Syntax_getTailPos_x3f(v___y_316_, v___y_319_);
lean_dec(v___y_316_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_inc(v___y_321_);
v___y_289_ = v___y_314_;
v___y_290_ = v___y_315_;
v___y_291_ = v___y_321_;
v___y_292_ = v___y_317_;
v___y_293_ = v___y_318_;
v___y_294_ = v___y_319_;
v___y_295_ = v___y_320_;
v___y_296_ = v___y_321_;
goto v___jp_288_;
}
else
{
lean_object* v_val_323_; 
v_val_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v___x_322_, 1);
v___y_289_ = v___y_314_;
v___y_290_ = v___y_315_;
v___y_291_ = v___y_321_;
v___y_292_ = v___y_317_;
v___y_293_ = v___y_318_;
v___y_294_ = v___y_319_;
v___y_295_ = v___y_320_;
v___y_296_ = v_val_323_;
goto v___jp_288_;
}
}
v___jp_324_:
{
lean_object* v_ref_332_; lean_object* v___x_333_; 
v_ref_332_ = l_Lean_replaceRef(v_ref_245_, v___y_330_);
v___x_333_ = l_Lean_Syntax_getPos_x3f(v_ref_332_, v___y_328_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___y_314_ = v___y_325_;
v___y_315_ = v___y_331_;
v___y_316_ = v_ref_332_;
v___y_317_ = v___y_326_;
v___y_318_ = v___y_327_;
v___y_319_ = v___y_328_;
v___y_320_ = v___y_329_;
v___y_321_ = v___x_334_;
goto v___jp_313_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_333_, 1);
v___y_314_ = v___y_325_;
v___y_315_ = v___y_331_;
v___y_316_ = v_ref_332_;
v___y_317_ = v___y_326_;
v___y_318_ = v___y_327_;
v___y_319_ = v___y_328_;
v___y_320_ = v___y_329_;
v___y_321_ = v_val_335_;
goto v___jp_313_;
}
}
v___jp_337_:
{
if (v___y_344_ == 0)
{
v___y_325_ = v___y_342_;
v___y_326_ = v___y_338_;
v___y_327_ = v___y_339_;
v___y_328_ = v___y_343_;
v___y_329_ = v___y_340_;
v___y_330_ = v___y_341_;
v___y_331_ = v_severity_247_;
goto v___jp_324_;
}
else
{
v___y_325_ = v___y_342_;
v___y_326_ = v___y_338_;
v___y_327_ = v___y_339_;
v___y_328_ = v___y_343_;
v___y_329_ = v___y_340_;
v___y_330_ = v___y_341_;
v___y_331_ = v___x_336_;
goto v___jp_324_;
}
}
v___jp_345_:
{
if (v___y_346_ == 0)
{
lean_object* v_fileName_347_; lean_object* v_fileMap_348_; lean_object* v_options_349_; lean_object* v_ref_350_; uint8_t v_suppressElabErrors_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___f_354_; uint8_t v___x_355_; uint8_t v___x_356_; 
v_fileName_347_ = lean_ctor_get(v___y_249_, 0);
v_fileMap_348_ = lean_ctor_get(v___y_249_, 1);
v_options_349_ = lean_ctor_get(v___y_249_, 2);
v_ref_350_ = lean_ctor_get(v___y_249_, 5);
v_suppressElabErrors_351_ = lean_ctor_get_uint8(v___y_249_, sizeof(void*)*14 + 1);
v___x_352_ = lean_box(v___y_346_);
v___x_353_ = lean_box(v_suppressElabErrors_351_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_354_, 0, v___x_352_);
lean_closure_set(v___f_354_, 1, v___x_353_);
v___x_355_ = 1;
v___x_356_ = l_Lean_instBEqMessageSeverity_beq(v_severity_247_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_338_ = v_fileMap_348_;
v___y_339_ = v_fileName_347_;
v___y_340_ = v_suppressElabErrors_351_;
v___y_341_ = v_ref_350_;
v___y_342_ = v___f_354_;
v___y_343_ = v___y_346_;
v___y_344_ = v___x_356_;
goto v___jp_337_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = l_Lean_warningAsError;
v___x_358_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_349_, v___x_357_);
v___y_338_ = v_fileMap_348_;
v___y_339_ = v_fileName_347_;
v___y_340_ = v_suppressElabErrors_351_;
v___y_341_ = v_ref_350_;
v___y_342_ = v___f_354_;
v___y_343_ = v___y_346_;
v___y_344_ = v___x_358_;
goto v___jp_337_;
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v_msgData_246_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_ref_363_, lean_object* v_msgData_364_, lean_object* v_severity_365_, lean_object* v_isSilent_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_severity_boxed_370_; uint8_t v_isSilent_boxed_371_; lean_object* v_res_372_; 
v_severity_boxed_370_ = lean_unbox(v_severity_365_);
v_isSilent_boxed_371_ = lean_unbox(v_isSilent_366_);
v_res_372_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_363_, v_msgData_364_, v_severity_boxed_370_, v_isSilent_boxed_371_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_ref_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_373_, uint8_t v_severity_374_, uint8_t v_isSilent_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_ref_379_; lean_object* v___x_380_; 
v_ref_379_ = lean_ctor_get(v___y_376_, 5);
v___x_380_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_379_, v_msgData_373_, v_severity_374_, v_isSilent_375_, v___y_376_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_381_, lean_object* v_severity_382_, lean_object* v_isSilent_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_severity_boxed_387_; uint8_t v_isSilent_boxed_388_; lean_object* v_res_389_; 
v_severity_boxed_387_ = lean_unbox(v_severity_382_);
v_isSilent_boxed_388_ = lean_unbox(v_isSilent_383_);
v_res_389_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2(v_msgData_381_, v_severity_boxed_387_, v_isSilent_boxed_388_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(lean_object* v_msgData_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = 1;
v___x_395_ = 0;
v___x_396_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2(v_msgData_390_, v___x_394_, v___x_395_, v___y_391_, v___y_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v_msgData_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_ref_406_; lean_object* v___x_407_; lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_416_; 
v_ref_406_ = lean_ctor_get(v___y_403_, 5);
v___x_407_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(v_msg_402_, v___y_403_, v___y_404_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_416_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_inc(v_ref_406_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_ref_406_);
lean_ctor_set(v___x_412_, 1, v_a_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v_msg_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_env_426_; lean_object* v___x_427_; lean_object* v_toEnvExtension_428_; lean_object* v_asyncMode_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_merged_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v___x_425_ = lean_st_ref_get(v___y_423_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_428_ = lean_ctor_get(v___x_427_, 0);
v_asyncMode_429_ = lean_ctor_get(v_toEnvExtension_428_, 2);
v___x_430_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_431_ = lean_box(0);
v___x_432_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_430_, v___x_427_, v_env_426_, v_asyncMode_429_, v___x_431_);
v_merged_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_432_, 1);
lean_dec(v_unused_442_);
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_merged_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v_merged_433_);
lean_ctor_set(v___x_435_, 0, v_o_422_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_o_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_merged_433_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_443_, v___y_444_);
lean_dec(v___y_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3(lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_options_450_; lean_object* v___x_451_; 
v_options_450_ = lean_ctor_get(v___y_447_, 2);
lean_inc_ref(v_options_450_);
v___x_451_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(v_options_450_, v___y_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3(v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(lean_object* v_keys_456_, lean_object* v_i_457_, lean_object* v_k_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_array_get_size(v_keys_456_);
v___x_460_ = lean_nat_dec_lt(v_i_457_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_i_457_);
return v___x_460_;
}
else
{
lean_object* v_k_x27_461_; uint8_t v___x_462_; 
v_k_x27_461_ = lean_array_fget_borrowed(v_keys_456_, v_i_457_);
v___x_462_ = l_Lean_instBEqExtraModUse_beq(v_k_458_, v_k_x27_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v_i_457_, v___x_463_);
lean_dec(v_i_457_);
v_i_457_ = v___x_464_;
goto _start;
}
else
{
lean_dec(v_i_457_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_keys_466_, lean_object* v_i_467_, lean_object* v_k_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_466_, v_i_467_, v_k_468_);
lean_dec_ref(v_k_468_);
lean_dec_ref(v_keys_466_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_x_471_, size_t v_x_472_, lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v_es_474_; lean_object* v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v_j_478_; lean_object* v___x_479_; 
v_es_474_ = lean_ctor_get(v_x_471_, 0);
v___x_475_ = lean_box(2);
v___x_476_ = ((size_t)31ULL);
v___x_477_ = lean_usize_land(v_x_472_, v___x_476_);
v_j_478_ = lean_usize_to_nat(v___x_477_);
v___x_479_ = lean_array_get_borrowed(v___x_475_, v_es_474_, v_j_478_);
lean_dec(v_j_478_);
switch(lean_obj_tag(v___x_479_))
{
case 0:
{
lean_object* v_key_480_; uint8_t v___x_481_; 
v_key_480_ = lean_ctor_get(v___x_479_, 0);
v___x_481_ = l_Lean_instBEqExtraModUse_beq(v_x_473_, v_key_480_);
return v___x_481_;
}
case 1:
{
lean_object* v_node_482_; size_t v___x_483_; size_t v___x_484_; 
v_node_482_ = lean_ctor_get(v___x_479_, 0);
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_usize_shift_right(v_x_472_, v___x_483_);
v_x_471_ = v_node_482_;
v_x_472_ = v___x_484_;
goto _start;
}
default: 
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
}
}
else
{
lean_object* v_ks_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_ks_487_ = lean_ctor_get(v_x_471_, 0);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_ks_487_, v___x_488_, v_x_473_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
size_t v_x_16560__boxed_493_; uint8_t v_res_494_; lean_object* v_r_495_; 
v_x_16560__boxed_493_ = lean_unbox_usize(v_x_491_);
lean_dec(v_x_491_);
v_res_494_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_490_, v_x_16560__boxed_493_, v_x_492_);
lean_dec_ref(v_x_492_);
lean_dec_ref(v_x_490_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint64_t v___x_498_; size_t v___x_499_; uint8_t v___x_500_; 
v___x_498_ = l_Lean_instHashableExtraModUse_hash(v_x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_496_, v___x_499_, v_x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_501_, v_x_502_);
lean_dec_ref(v_x_502_);
lean_dec_ref(v_x_501_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_505_; double v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_float_of_nat(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_cls_509_, lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_ref_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_560_; 
v_ref_514_ = lean_ctor_get(v___y_511_, 5);
v___x_515_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(v_msg_510_, v___y_511_, v___y_512_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_560_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_560_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_560_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v_traceState_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_cache_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_559_; 
v___x_520_ = lean_st_ref_take(v___y_512_);
v_traceState_521_ = lean_ctor_get(v___x_520_, 4);
v_env_522_ = lean_ctor_get(v___x_520_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_520_, 1);
v_ngen_524_ = lean_ctor_get(v___x_520_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_520_, 3);
v_cache_526_ = lean_ctor_get(v___x_520_, 5);
v_messages_527_ = lean_ctor_get(v___x_520_, 6);
v_infoState_528_ = lean_ctor_get(v___x_520_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_520_, 8);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_559_ == 0)
{
v___x_531_ = v___x_520_;
v_isShared_532_ = v_isSharedCheck_559_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_520_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_559_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint64_t v_tid_533_; lean_object* v_traces_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_558_; 
v_tid_533_ = lean_ctor_get_uint64(v_traceState_521_, sizeof(void*)*1);
v_traces_534_ = lean_ctor_get(v_traceState_521_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_traceState_521_);
if (v_isSharedCheck_558_ == 0)
{
v___x_536_ = v_traceState_521_;
v_isShared_537_ = v_isSharedCheck_558_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_traces_534_);
lean_dec(v_traceState_521_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_558_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; double v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_538_ = lean_box(0);
v___x_539_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0);
v___x_540_ = 0;
v___x_541_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_542_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_542_, 0, v_cls_509_);
lean_ctor_set(v___x_542_, 1, v___x_538_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
lean_ctor_set_float(v___x_542_, sizeof(void*)*3, v___x_539_);
lean_ctor_set_float(v___x_542_, sizeof(void*)*3 + 8, v___x_539_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*3 + 16, v___x_540_);
v___x_543_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1));
v___x_544_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v_a_516_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
lean_inc(v_ref_514_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_ref_514_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_PersistentArray_push___redArg(v_traces_534_, v___x_545_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_546_);
v___x_548_ = v___x_536_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_546_);
lean_ctor_set_uint64(v_reuseFailAlloc_557_, sizeof(void*)*1, v_tid_533_);
v___x_548_ = v_reuseFailAlloc_557_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v___x_548_);
v___x_550_ = v___x_531_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_snapshotTasks_529_);
v___x_550_ = v_reuseFailAlloc_556_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = lean_st_ref_put(v___y_512_, v___x_550_);
v___x_552_ = lean_box(0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_552_);
v___x_554_ = v___x_518_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_cls_561_, lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_561_, v_msg_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_571_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_572_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_587_ = l_Lean_stringToMessageData(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_cls_590_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_591_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_592_ = l_Lean_Name_append(v___x_591_, v_cls_590_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_603_, uint8_t v_isMeta_604_, lean_object* v_hint_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; lean_object* v_env_610_; uint8_t v_isExporting_611_; lean_object* v___x_612_; lean_object* v_env_613_; lean_object* v___x_614_; lean_object* v_entry_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___y_620_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_609_ = lean_st_ref_get(v___y_607_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v_isExporting_611_ = lean_ctor_get_uint8(v_env_610_, sizeof(void*)*8);
lean_dec_ref(v_env_610_);
v___x_612_ = lean_st_ref_get(v___y_607_);
v_env_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_ref(v_env_613_);
lean_dec(v___x_612_);
v___x_614_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_603_);
v_entry_615_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_615_, 0, v_mod_603_);
lean_ctor_set_uint8(v_entry_615_, sizeof(void*)*1, v_isExporting_611_);
lean_ctor_set_uint8(v_entry_615_, sizeof(void*)*1 + 1, v_isMeta_604_);
v___x_616_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_617_ = lean_box(1);
v___x_618_ = lean_box(0);
v___x_645_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_614_, v___x_616_, v_env_613_, v___x_617_, v___x_618_);
v___x_646_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v___x_645_, v_entry_615_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v_options_647_; uint8_t v_hasTrace_648_; 
v_options_647_ = lean_ctor_get(v___y_606_, 2);
v_hasTrace_648_ = lean_ctor_get_uint8(v_options_647_, sizeof(void*)*1);
if (v_hasTrace_648_ == 0)
{
lean_dec(v_hint_605_);
lean_dec(v_mod_603_);
v___y_620_ = v___y_607_;
goto v___jp_619_;
}
else
{
lean_object* v_inheritedTraceOptions_649_; lean_object* v_cls_650_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_inheritedTraceOptions_649_ = lean_ctor_get(v___y_606_, 13);
v_cls_650_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_670_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_649_, v_options_647_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_hint_605_);
lean_dec(v_mod_603_);
v___y_620_ = v___y_607_;
goto v___jp_619_;
}
else
{
lean_object* v___x_672_; lean_object* v___y_674_; 
v___x_672_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16);
if (v_isExporting_611_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_674_ = v___x_681_;
goto v___jp_673_;
}
else
{
lean_object* v___x_682_; 
v___x_682_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__22));
v___y_674_ = v___x_682_;
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc_ref(v___y_674_);
v___x_675_ = l_Lean_stringToMessageData(v___y_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_672_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
if (v_isMeta_604_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_657_ = v___x_678_;
v___y_658_ = v___x_679_;
goto v___jp_656_;
}
else
{
lean_object* v___x_680_; 
v___x_680_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__20));
v___y_657_ = v___x_678_;
v___y_658_ = v___x_680_;
goto v___jp_656_;
}
}
}
v___jp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___y_652_);
lean_ctor_set(v___x_654_, 1, v___y_653_);
v___x_655_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_650_, v___x_654_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
v___y_620_ = v___y_607_;
goto v___jp_619_;
}
else
{
lean_dec_ref_known(v_entry_615_, 1);
return v___x_655_;
}
}
v___jp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
lean_inc_ref(v___y_658_);
v___x_659_ = l_Lean_stringToMessageData(v___y_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_657_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_MessageData_ofName(v_mod_603_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_Name_isAnonymous(v_hint_605_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_667_ = l_Lean_MessageData_ofName(v_hint_605_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___y_652_ = v___x_664_;
v___y_653_ = v___x_668_;
goto v___jp_651_;
}
else
{
lean_object* v___x_669_; 
lean_dec(v_hint_605_);
v___x_669_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___y_652_ = v___x_664_;
v___y_653_ = v___x_669_;
goto v___jp_651_;
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref_known(v_entry_615_, 1);
lean_dec(v_hint_605_);
lean_dec(v_mod_603_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v_toEnvExtension_622_; lean_object* v_env_623_; lean_object* v_nextMacroScope_624_; lean_object* v_ngen_625_; lean_object* v_auxDeclNGen_626_; lean_object* v_traceState_627_; lean_object* v_messages_628_; lean_object* v_infoState_629_; lean_object* v_snapshotTasks_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_643_; 
v___x_621_ = lean_st_ref_take(v___y_620_);
v_toEnvExtension_622_ = lean_ctor_get(v___x_616_, 0);
v_env_623_ = lean_ctor_get(v___x_621_, 0);
v_nextMacroScope_624_ = lean_ctor_get(v___x_621_, 1);
v_ngen_625_ = lean_ctor_get(v___x_621_, 2);
v_auxDeclNGen_626_ = lean_ctor_get(v___x_621_, 3);
v_traceState_627_ = lean_ctor_get(v___x_621_, 4);
v_messages_628_ = lean_ctor_get(v___x_621_, 6);
v_infoState_629_ = lean_ctor_get(v___x_621_, 7);
v_snapshotTasks_630_ = lean_ctor_get(v___x_621_, 8);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_621_, 5);
lean_dec(v_unused_644_);
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_643_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snapshotTasks_630_);
lean_inc(v_infoState_629_);
lean_inc(v_messages_628_);
lean_inc(v_traceState_627_);
lean_inc(v_auxDeclNGen_626_);
lean_inc(v_ngen_625_);
lean_inc(v_nextMacroScope_624_);
lean_inc(v_env_623_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_643_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_asyncMode_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v_asyncMode_634_ = lean_ctor_get(v_toEnvExtension_622_, 2);
v___x_635_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_616_, v_env_623_, v_entry_615_, v_asyncMode_634_, v___x_618_);
v___x_636_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 5, v___x_636_);
lean_ctor_set(v___x_632_, 0, v___x_635_);
v___x_638_ = v___x_632_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_nextMacroScope_624_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_ngen_625_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_auxDeclNGen_626_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v_traceState_627_);
lean_ctor_set(v_reuseFailAlloc_642_, 5, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_642_, 6, v_messages_628_);
lean_ctor_set(v_reuseFailAlloc_642_, 7, v_infoState_629_);
lean_ctor_set(v_reuseFailAlloc_642_, 8, v_snapshotTasks_630_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_st_ref_put(v___y_620_, v___x_638_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_685_, lean_object* v_isMeta_686_, lean_object* v_hint_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_isMeta_boxed_691_; lean_object* v_res_692_; 
v_isMeta_boxed_691_ = lean_unbox(v_isMeta_686_);
v_res_692_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_mod_685_, v_isMeta_boxed_691_, v_hint_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_693_, lean_object* v_declName_694_, lean_object* v_as_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v_declName_694_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_b_698_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v_modules_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v_toImport_709_; lean_object* v_module_710_; uint8_t v___x_711_; lean_object* v___x_712_; 
v___x_704_ = l_Lean_Environment_header(v___x_693_);
v_modules_705_ = lean_ctor_get(v___x_704_, 3);
lean_inc_ref(v_modules_705_);
lean_dec_ref(v___x_704_);
v___x_706_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_707_ = lean_array_uget_borrowed(v_as_695_, v_i_697_);
v___x_708_ = lean_array_get(v___x_706_, v_modules_705_, v_a_707_);
lean_dec_ref(v_modules_705_);
v_toImport_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_toImport_709_);
lean_dec(v___x_708_);
v_module_710_ = lean_ctor_get(v_toImport_709_, 0);
lean_inc(v_module_710_);
lean_dec_ref(v_toImport_709_);
v___x_711_ = 0;
lean_inc(v_declName_694_);
v___x_712_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_module_710_, v___x_711_, v_declName_694_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; 
lean_dec_ref_known(v___x_712_, 1);
v___x_713_ = lean_box(0);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_697_, v___x_714_);
v_i_697_ = v___x_715_;
v_b_698_ = v___x_713_;
goto _start;
}
else
{
lean_dec(v_declName_694_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_717_, lean_object* v_declName_718_, lean_object* v_as_719_, lean_object* v_sz_720_, lean_object* v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
size_t v_sz_boxed_726_; size_t v_i_boxed_727_; lean_object* v_res_728_; 
v_sz_boxed_726_ = lean_unbox_usize(v_sz_720_);
lean_dec(v_sz_720_);
v_i_boxed_727_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(v___x_717_, v_declName_718_, v_as_719_, v_sz_boxed_726_, v_i_boxed_727_, v_b_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v_as_719_);
lean_dec_ref(v___x_717_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg(lean_object* v_m_729_, lean_object* v_query_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_zero_734_; uint8_t v_isZero_735_; 
v_zero_734_ = lean_unsigned_to_nat(0u);
v_isZero_735_ = lean_nat_dec_eq(v_x_732_, v_zero_734_);
if (v_isZero_735_ == 1)
{
lean_dec(v_x_733_);
lean_dec(v_x_732_);
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(2);
return v___x_736_;
}
else
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_val_737_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v_x_731_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v_x_731_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_keyArray_745_; lean_object* v_valueArray_746_; lean_object* v___x_747_; uint8_t v_isSome_748_; 
v_keyArray_745_ = lean_ctor_get(v_m_729_, 1);
v_valueArray_746_ = lean_ctor_get(v_m_729_, 2);
v___x_747_ = lean_array_fget_borrowed(v_keyArray_745_, v_x_733_);
v_isSome_748_ = lean_noption_is_some(v___x_747_);
if (v_isSome_748_ == 0)
{
lean_dec(v_x_732_);
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_x_733_);
return v___x_749_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_x_733_);
v_val_750_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v_x_731_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_val_750_);
lean_dec(v_x_731_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_val_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_one_758_; lean_object* v_n_759_; lean_object* v___y_761_; 
v_one_758_ = lean_unsigned_to_nat(1u);
v_n_759_ = lean_nat_sub(v_x_732_, v_one_758_);
lean_dec(v_x_732_);
if (v_isSome_748_ == 0)
{
goto v___jp_767_;
}
else
{
lean_object* v___x_769_; uint8_t v_isSome_770_; 
v___x_769_ = lean_array_fget_borrowed(v_valueArray_746_, v_x_733_);
v_isSome_770_ = lean_noption_is_some(v___x_769_);
if (v_isSome_770_ == 0)
{
goto v___jp_767_;
}
else
{
lean_object* v_val_771_; uint8_t v___x_772_; 
lean_inc(v___x_747_);
v_val_771_ = lean_noption_get(v___x_747_);
v___x_772_ = lean_name_eq(v_val_771_, v_query_730_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
lean_dec(v_val_771_);
v___x_773_ = lean_array_get_size(v_keyArray_745_);
v___x_774_ = lean_nat_add(v_x_733_, v_one_758_);
lean_dec(v_x_733_);
v___x_775_ = lean_nat_dec_lt(v___x_774_, v___x_773_);
if (v___x_775_ == 0)
{
lean_dec(v___x_774_);
v_x_732_ = v_n_759_;
v_x_733_ = v_zero_734_;
goto _start;
}
else
{
v_x_732_ = v_n_759_;
v_x_733_ = v___x_774_;
goto _start;
}
}
else
{
lean_object* v_val_778_; lean_object* v___x_779_; 
lean_dec(v_n_759_);
lean_dec(v_x_731_);
lean_inc(v___x_769_);
v_val_778_ = lean_noption_get(v___x_769_);
v___x_779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_779_, 0, v_x_733_);
lean_ctor_set(v___x_779_, 1, v_val_771_);
lean_ctor_set(v___x_779_, 2, v_val_778_);
return v___x_779_;
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_array_get_size(v_keyArray_745_);
v___x_763_ = lean_nat_add(v_x_733_, v_one_758_);
lean_dec(v_x_733_);
v___x_764_ = lean_nat_dec_lt(v___x_763_, v___x_762_);
if (v___x_764_ == 0)
{
lean_dec(v___x_763_);
v_x_731_ = v___y_761_;
v_x_732_ = v_n_759_;
v_x_733_ = v_zero_734_;
goto _start;
}
else
{
v_x_731_ = v___y_761_;
v_x_732_ = v_n_759_;
v_x_733_ = v___x_763_;
goto _start;
}
}
v___jp_767_:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v___x_768_; 
lean_inc(v_x_733_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v_x_733_);
v___y_761_ = v___x_768_;
goto v___jp_760_;
}
else
{
v___y_761_ = v_x_731_;
goto v___jp_760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg___boxed(lean_object* v_m_780_, lean_object* v_query_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg(v_m_780_, v_query_781_, v_x_782_, v_x_783_, v_x_784_);
lean_dec(v_query_781_);
lean_dec_ref(v_m_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg(lean_object* v_m_786_, lean_object* v_query_787_){
_start:
{
lean_object* v_keyArray_788_; lean_object* v___x_789_; uint64_t v___y_791_; 
v_keyArray_788_ = lean_ctor_get(v_m_786_, 1);
v___x_789_ = lean_array_get_size(v_keyArray_788_);
if (lean_obj_tag(v_query_787_) == 0)
{
uint64_t v___x_806_; 
v___x_806_ = 1723ULL;
v___y_791_ = v___x_806_;
goto v___jp_790_;
}
else
{
uint64_t v_hash_807_; 
v_hash_807_ = lean_ctor_get_uint64(v_query_787_, sizeof(void*)*2);
v___y_791_ = v_hash_807_;
goto v___jp_790_;
}
v___jp_790_:
{
uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v_fold_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_792_ = 32ULL;
v___x_793_ = lean_uint64_shift_right(v___y_791_, v___x_792_);
v_fold_794_ = lean_uint64_xor(v___y_791_, v___x_793_);
v___x_795_ = 16ULL;
v___x_796_ = lean_uint64_shift_right(v_fold_794_, v___x_795_);
v___x_797_ = lean_uint64_xor(v_fold_794_, v___x_796_);
v___x_798_ = lean_uint64_to_usize(v___x_797_);
v___x_799_ = lean_usize_of_nat(v___x_789_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_sub(v___x_799_, v___x_800_);
v___x_802_ = lean_usize_land(v___x_798_, v___x_801_);
v___x_803_ = lean_usize_to_nat(v___x_802_);
v___x_804_ = lean_box(0);
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg(v_m_786_, v_query_787_, v___x_804_, v___x_789_, v___x_803_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg___boxed(lean_object* v_m_808_, lean_object* v_query_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg(v_m_808_, v_query_809_);
lean_dec(v_query_809_);
lean_dec_ref(v_m_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object* v_m_811_, lean_object* v_query_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg(v_m_811_, v_query_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_index_814_; lean_object* v_key_815_; lean_object* v_value_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_index_814_ = lean_ctor_get(v___x_813_, 0);
v_key_815_ = lean_ctor_get(v___x_813_, 1);
v_value_816_ = lean_ctor_get(v___x_813_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_value_816_);
lean_inc(v_key_815_);
lean_inc(v_index_814_);
lean_dec(v___x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_index_814_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_key_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_value_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v___x_824_; 
lean_dec(v___x_813_);
v___x_824_ = lean_box(1);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_m_825_, lean_object* v_query_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_m_825_, v_query_826_);
lean_dec(v_query_826_);
lean_dec_ref(v_m_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_m_828_, v_a_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_value_831_; lean_object* v___x_832_; 
v_value_831_ = lean_ctor_get(v___x_830_, 2);
lean_inc(v_value_831_);
lean_dec_ref_known(v___x_830_, 3);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_value_831_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = lean_box(0);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_m_834_);
return v_res_836_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__1));
v___x_840_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__0));
v___x_841_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_840_, v___x_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(lean_object* v_declName_844_, uint8_t v_isMeta_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_env_853_; lean_object* v___y_855_; lean_object* v___x_868_; 
v___x_849_ = lean_st_ref_get(v___y_847_);
v_env_853_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_env_853_);
lean_dec(v___x_849_);
v___x_868_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_853_, v_declName_844_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_dec_ref(v_env_853_);
lean_dec(v_declName_844_);
goto v___jp_850_;
}
else
{
lean_object* v_val_869_; lean_object* v___x_870_; lean_object* v_modules_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_val_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = l_Lean_Environment_header(v_env_853_);
v_modules_871_ = lean_ctor_get(v___x_870_, 3);
lean_inc_ref(v_modules_871_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_array_get_size(v_modules_871_);
v___x_873_ = lean_nat_dec_lt(v_val_869_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_modules_871_);
lean_dec(v_val_869_);
lean_dec_ref(v_env_853_);
lean_dec(v_declName_844_);
goto v___jp_850_;
}
else
{
lean_object* v___x_874_; lean_object* v_env_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___y_879_; 
v___x_874_ = lean_st_ref_get(v___y_847_);
v_env_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_env_875_);
lean_dec(v___x_874_);
v___x_876_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2);
v___x_877_ = lean_array_fget(v_modules_871_, v_val_869_);
lean_dec(v_val_869_);
lean_dec_ref(v_modules_871_);
if (v_isMeta_845_ == 0)
{
lean_dec_ref(v_env_875_);
v___y_879_ = v_isMeta_845_;
goto v___jp_878_;
}
else
{
uint8_t v___x_890_; 
lean_inc(v_declName_844_);
v___x_890_ = l_Lean_isMarkedMeta(v_env_875_, v_declName_844_);
if (v___x_890_ == 0)
{
v___y_879_ = v_isMeta_845_;
goto v___jp_878_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = 0;
v___y_879_ = v___x_891_;
goto v___jp_878_;
}
}
v___jp_878_:
{
lean_object* v_toImport_880_; lean_object* v_module_881_; lean_object* v___x_882_; 
v_toImport_880_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_toImport_880_);
lean_dec(v___x_877_);
v_module_881_ = lean_ctor_get(v_toImport_880_, 0);
lean_inc(v_module_881_);
lean_dec_ref(v_toImport_880_);
lean_inc(v_declName_844_);
v___x_882_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_module_881_, v___y_879_, v_declName_844_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref_known(v___x_882_, 1);
v___x_883_ = l_Lean_indirectModUseExt;
v___x_884_ = lean_box(1);
v___x_885_ = lean_box(0);
lean_inc_ref(v_env_853_);
v___x_886_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_876_, v___x_883_, v_env_853_, v___x_884_, v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_886_, v_declName_844_);
lean_dec(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__3));
v___y_855_ = v___x_888_;
goto v___jp_854_;
}
else
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_887_, 1);
v___y_855_ = v_val_889_;
goto v___jp_854_;
}
}
else
{
lean_dec_ref(v_env_853_);
lean_dec(v_declName_844_);
return v___x_882_;
}
}
}
}
v___jp_850_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
v___jp_854_:
{
lean_object* v___x_856_; size_t v_sz_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v_sz_857_ = lean_array_size(v___y_855_);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(v_env_853_, v_declName_844_, v___y_855_, v_sz_857_, v___x_858_, v___x_856_, v___y_846_, v___y_847_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v_env_853_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_859_, 0);
lean_dec(v_unused_867_);
v___x_861_ = v___x_859_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_dec(v___x_859_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_856_);
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_856_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_892_, lean_object* v_isMeta_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_isMeta_boxed_897_; lean_object* v_res_898_; 
v_isMeta_boxed_897_ = lean_unbox(v_isMeta_893_);
v_res_898_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(v_declName_892_, v_isMeta_boxed_897_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_898_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_903_ = l_Lean_MessageData_ofFormat(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_908_ = l_Lean_MessageData_ofFormat(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_922_ = l_Lean_MessageData_ofFormat(v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_924_ = l_Lean_MessageData_hint_x27(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_932_ = l_Lean_MessageData_ofFormat(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_940_ = l_Lean_MessageData_ofFormat(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_947_ = l_Lean_MessageData_ofFormat(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_951_ = lean_box(1);
v___x_952_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_953_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_ctor_set(v___x_954_, 2, v___x_951_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
lean_ctor_set(v___x_959_, 3, v___x_958_);
lean_ctor_set(v___x_959_, 4, v___x_957_);
lean_ctor_set(v___x_959_, 5, v___x_957_);
lean_ctor_set(v___x_959_, 6, v___x_957_);
lean_ctor_set(v___x_959_, 7, v___x_957_);
lean_ctor_set(v___x_959_, 8, v___x_957_);
lean_ctor_set(v___x_959_, 9, v___x_957_);
lean_ctor_set(v___x_959_, 10, v___x_957_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
lean_ctor_set(v___x_961_, 3, v___x_960_);
lean_ctor_set(v___x_961_, 4, v___x_960_);
lean_ctor_set(v___x_961_, 5, v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
lean_ctor_set(v___x_963_, 3, v___x_962_);
lean_ctor_set(v___x_963_, 4, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_964_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_966_ = lean_box(1);
v___x_967_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_968_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_966_);
lean_ctor_set(v___x_969_, 3, v___x_965_);
lean_ctor_set(v___x_969_, 4, v___x_964_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v___f_978_, lean_object* v_declName_979_, lean_object* v_stx_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v_hint_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; 
v___x_990_ = l_Lean_Name_mkStr2(v___x_976_, v___x_977_);
lean_inc(v_stx_980_);
v___x_991_ = l_Lean_Syntax_isOfKind(v_stx_980_, v___x_990_);
lean_dec(v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_stx_980_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1101_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1100_, v___y_981_, v___y_982_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v_val_1114_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1155_; uint8_t v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v_a_1163_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v_a_1240_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_since_x3f_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v_typeChanged_x3f_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1296_; lean_object* v_text_x3f_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v_id_x3f_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1322_ = l_Lean_Syntax_getArg(v_stx_980_, v___x_1103_);
v___x_1323_ = l_Lean_Syntax_isNone(v___x_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
lean_inc(v___x_1322_);
v___x_1324_ = l_Lean_Syntax_matchesNull(v___x_1322_, v___x_1103_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v___x_1322_);
lean_dec(v_stx_980_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___x_1325_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1326_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1325_, v___y_981_, v___y_982_);
return v___x_1326_;
}
else
{
lean_object* v_id_x3f_1327_; lean_object* v___x_1328_; 
v_id_x3f_1327_ = l_Lean_Syntax_getArg(v___x_1322_, v___x_1102_);
lean_dec(v___x_1322_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_id_x3f_1327_);
v_id_x3f_1310_ = v___x_1328_;
v___y_1311_ = v___y_981_;
v___y_1312_ = v___y_982_;
goto v___jp_1309_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec(v___x_1322_);
v___x_1329_ = lean_box(0);
v_id_x3f_1310_ = v___x_1329_;
v___y_1311_ = v___y_981_;
v___y_1312_ = v___y_982_;
goto v___jp_1309_;
}
v___jp_1104_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1115_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___f_978_);
v___x_1120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1116_);
lean_ctor_set(v___x_1120_, 1, v___x_1117_);
lean_ctor_set(v___x_1120_, 2, v___x_1117_);
lean_ctor_set(v___x_1120_, 3, v___x_1117_);
lean_ctor_set(v___x_1120_, 4, v___x_1118_);
lean_ctor_set(v___x_1120_, 5, v___x_1119_);
lean_inc(v_val_1114_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_val_1114_);
lean_ctor_set(v___x_1121_, 1, v_val_1114_);
v___x_1122_ = l_Lean_Syntax_ofRange(v___x_1121_, v___x_991_);
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
v___x_1124_ = 4;
v___x_1125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1125_, 0, v___x_1120_);
lean_ctor_set(v___x_1125_, 1, v___x_1123_);
lean_ctor_set(v___x_1125_, 2, v___x_1117_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*3, v___x_1124_);
v___x_1126_ = lean_mk_empty_array_with_capacity(v___x_1103_);
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1125_);
v___x_1128_ = l_Lean_MessageData_hint(v___x_1115_, v___x_1127_, v___x_1117_, v___x_1117_, v___y_1107_, v___y_1106_, v___y_1111_);
lean_dec_ref(v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___y_1060_ = v___y_1105_;
v___y_1061_ = v___y_1108_;
v___y_1062_ = v___y_1109_;
v___y_1063_ = v___y_1110_;
v___y_1064_ = v___y_1112_;
v___y_1065_ = v___y_1113_;
v_hint_1066_ = v_a_1129_;
v___y_1067_ = v___y_1106_;
v___y_1068_ = v___y_1111_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1105_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1138_:
{
if (lean_obj_tag(v___y_1139_) == 0)
{
lean_dec_ref(v___f_978_);
v___y_1091_ = v___y_1139_;
v___y_1092_ = v___y_1140_;
v___y_1093_ = v___y_1141_;
v___y_1094_ = v___y_1143_;
v___y_1095_ = v___y_1144_;
v___y_1096_ = v___y_1145_;
v___y_1097_ = v___y_1146_;
v___y_1098_ = v___y_1147_;
goto v___jp_1090_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1149_; 
v_val_1148_ = lean_ctor_get(v___y_1139_, 0);
v___x_1149_ = l_Lean_Syntax_getTailPos_x3f(v_val_1148_, v___x_991_);
if (lean_obj_tag(v___x_1149_) == 1)
{
lean_object* v_val_1150_; 
v_val_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_val_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___y_1105_ = v___y_1139_;
v___y_1106_ = v___y_1140_;
v___y_1107_ = v___y_1142_;
v___y_1108_ = v___y_1141_;
v___y_1109_ = v___y_1143_;
v___y_1110_ = v___y_1144_;
v___y_1111_ = v___y_1145_;
v___y_1112_ = v___y_1146_;
v___y_1113_ = v___y_1147_;
v_val_1114_ = v_val_1150_;
goto v___jp_1104_;
}
else
{
lean_dec(v___x_1149_);
lean_dec_ref(v___f_978_);
v___y_1091_ = v___y_1139_;
v___y_1092_ = v___y_1140_;
v___y_1093_ = v___y_1141_;
v___y_1094_ = v___y_1143_;
v___y_1095_ = v___y_1144_;
v___y_1096_ = v___y_1145_;
v___y_1097_ = v___y_1146_;
v___y_1098_ = v___y_1147_;
goto v___jp_1090_;
}
}
}
v___jp_1151_:
{
if (v_a_1163_ == 0)
{
if (lean_obj_tag(v___y_1160_) == 0)
{
if (v___y_1156_ == 0)
{
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1152_;
v___y_1044_ = v___y_1155_;
v___y_1045_ = v___y_1161_;
v___y_1046_ = v___y_1162_;
v___y_1047_ = v___y_1153_;
v___y_1048_ = v___y_1159_;
goto v___jp_1042_;
}
else
{
if (lean_obj_tag(v___y_1162_) == 0)
{
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___y_1153_;
v___y_1141_ = v___y_1155_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1157_;
v___y_1144_ = v___y_1158_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1161_;
v___y_1147_ = v___y_1162_;
goto v___jp_1138_;
}
else
{
lean_object* v_val_1164_; lean_object* v___x_1165_; 
v_val_1164_ = lean_ctor_get(v___y_1162_, 0);
v___x_1165_ = l_Lean_Syntax_getTailPos_x3f(v_val_1164_, v___x_991_);
if (lean_obj_tag(v___x_1165_) == 0)
{
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___y_1153_;
v___y_1141_ = v___y_1155_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1157_;
v___y_1144_ = v___y_1158_;
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1161_;
v___y_1147_ = v___y_1162_;
goto v___jp_1138_;
}
else
{
lean_object* v_val_1166_; 
v_val_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___y_1105_ = v___y_1152_;
v___y_1106_ = v___y_1153_;
v___y_1107_ = v___y_1154_;
v___y_1108_ = v___y_1155_;
v___y_1109_ = v___y_1157_;
v___y_1110_ = v___y_1158_;
v___y_1111_ = v___y_1159_;
v___y_1112_ = v___y_1161_;
v___y_1113_ = v___y_1162_;
v_val_1114_ = v_val_1166_;
goto v___jp_1104_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_1160_, 1);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1152_;
v___y_1044_ = v___y_1155_;
v___y_1045_ = v___y_1161_;
v___y_1046_ = v___y_1162_;
v___y_1047_ = v___y_1153_;
v___y_1048_ = v___y_1159_;
goto v___jp_1042_;
}
}
else
{
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___f_978_);
if (lean_obj_tag(v___y_1160_) == 0)
{
v___y_1043_ = v___y_1152_;
v___y_1044_ = v___y_1155_;
v___y_1045_ = v___y_1161_;
v___y_1046_ = v___y_1162_;
v___y_1047_ = v___y_1153_;
v___y_1048_ = v___y_1159_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref_known(v___y_1160_, 1);
v___x_1167_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1168_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_1167_, v___y_1153_, v___y_1159_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref_known(v___x_1168_, 1);
v___y_1043_ = v___y_1152_;
v___y_1044_ = v___y_1155_;
v___y_1045_ = v___y_1161_;
v___y_1046_ = v___y_1162_;
v___y_1047_ = v___y_1153_;
v___y_1048_ = v___y_1159_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v___y_1155_);
lean_dec(v___y_1152_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
v___jp_1177_:
{
if (lean_obj_tag(v___y_1181_) == 1)
{
lean_object* v_val_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
v_val_1185_ = lean_ctor_get(v___y_1181_, 0);
v___x_1186_ = 0;
lean_inc(v_val_1185_);
v___x_1187_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(v_val_1185_, v___x_1186_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1188_; lean_object* v_a_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
lean_dec_ref_known(v___x_1187_, 1);
v___x_1188_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3(v___y_1183_, v___y_1184_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = l_Lean_Linter_linter_deprecated;
v___x_1191_ = l_Lean_Linter_getLinterValue(v___x_1190_, v_a_1189_);
lean_dec(v_a_1189_);
if (v___x_1191_ == 0)
{
lean_dec(v___y_1180_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1178_;
v___y_1044_ = v___y_1179_;
v___y_1045_ = v___y_1181_;
v___y_1046_ = v___y_1182_;
v___y_1047_ = v___y_1183_;
v___y_1048_ = v___y_1184_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_st_ref_get(v___y_1184_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref_n(v_env_1193_, 2);
lean_dec(v___x_1192_);
v___x_1194_ = l_Lean_Environment_find_x3f(v_env_1193_, v_declName_979_, v___x_1186_);
if (lean_obj_tag(v___x_1194_) == 1)
{
lean_object* v_val_1195_; lean_object* v___x_1196_; 
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v___x_1194_, 1);
lean_inc(v_val_1185_);
v___x_1196_ = l_Lean_Environment_find_x3f(v_env_1193_, v_val_1185_, v___x_1186_);
if (lean_obj_tag(v___x_1196_) == 1)
{
lean_object* v_val_1197_; uint8_t v___x_1198_; uint8_t v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; uint64_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_val_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_val_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = 1;
v___x_1199_ = 0;
v___x_1200_ = 2;
v___x_1201_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1201_, 0, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 1, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 2, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 3, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 4, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 5, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 6, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 7, v___x_1186_);
lean_ctor_set_uint8(v___x_1201_, 8, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 9, v___x_1198_);
lean_ctor_set_uint8(v___x_1201_, 10, v___x_1199_);
lean_ctor_set_uint8(v___x_1201_, 11, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 12, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 13, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 14, v___x_1200_);
lean_ctor_set_uint8(v___x_1201_, 15, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 16, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 17, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 18, v___x_1191_);
lean_ctor_set_uint8(v___x_1201_, 19, v___x_1186_);
v___x_1202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set_uint64(v___x_1203_, sizeof(void*)*1, v___x_1202_);
v___x_1204_ = lean_box(1);
v___x_1205_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1206_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1208_, 0, v___x_1203_);
lean_ctor_set(v___x_1208_, 1, v___x_1204_);
lean_ctor_set(v___x_1208_, 2, v___x_1205_);
lean_ctor_set(v___x_1208_, 3, v___x_1206_);
lean_ctor_set(v___x_1208_, 4, v___x_1207_);
lean_ctor_set(v___x_1208_, 5, v___x_1102_);
lean_ctor_set(v___x_1208_, 6, v___x_1207_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*7, v___x_1186_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*7 + 1, v___x_1186_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*7 + 2, v___x_1186_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*7 + 3, v___x_991_);
v___x_1209_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1210_ = lean_st_mk_ref(v___x_1209_);
v___x_1211_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_1195_, v_val_1197_, v___x_1208_, v___x_1210_, v___y_1183_, v___y_1184_);
lean_dec_ref_known(v___x_1208_, 7);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = lean_st_ref_get(v___x_1210_);
lean_dec(v___x_1210_);
lean_dec(v___x_1213_);
v___x_1214_ = lean_unbox(v_a_1212_);
lean_dec(v_a_1212_);
v___y_1152_ = v___y_1178_;
v___y_1153_ = v___y_1183_;
v___y_1154_ = v___x_1186_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___x_1191_;
v___y_1157_ = v_val_1195_;
v___y_1158_ = v_val_1197_;
v___y_1159_ = v___y_1184_;
v___y_1160_ = v___y_1180_;
v___y_1161_ = v___y_1181_;
v___y_1162_ = v___y_1182_;
v_a_1163_ = v___x_1214_;
goto v___jp_1151_;
}
else
{
lean_dec(v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1215_; uint8_t v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1216_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
v___y_1152_ = v___y_1178_;
v___y_1153_ = v___y_1183_;
v___y_1154_ = v___x_1186_;
v___y_1155_ = v___y_1179_;
v___y_1156_ = v___x_1191_;
v___y_1157_ = v_val_1195_;
v___y_1158_ = v_val_1197_;
v___y_1159_ = v___y_1184_;
v___y_1160_ = v___y_1180_;
v___y_1161_ = v___y_1181_;
v___y_1162_ = v___y_1182_;
v_a_1163_ = v___x_1216_;
goto v___jp_1151_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_val_1197_);
lean_dec(v_val_1195_);
lean_dec_ref_known(v___y_1181_, 1);
lean_dec(v___y_1182_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___f_978_);
v_a_1217_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1211_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1211_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_dec(v___x_1196_);
lean_dec(v_val_1195_);
lean_dec(v___y_1180_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1178_;
v___y_1044_ = v___y_1179_;
v___y_1045_ = v___y_1181_;
v___y_1046_ = v___y_1182_;
v___y_1047_ = v___y_1183_;
v___y_1048_ = v___y_1184_;
goto v___jp_1042_;
}
}
else
{
lean_dec(v___x_1194_);
lean_dec_ref(v_env_1193_);
lean_dec(v___y_1180_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1178_;
v___y_1044_ = v___y_1179_;
v___y_1045_ = v___y_1181_;
v___y_1046_ = v___y_1182_;
v___y_1047_ = v___y_1183_;
v___y_1048_ = v___y_1184_;
goto v___jp_1042_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref_known(v___y_1181_, 1);
lean_dec(v___y_1182_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v_a_1225_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1187_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1187_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_dec(v___y_1180_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___y_1043_ = v___y_1178_;
v___y_1044_ = v___y_1179_;
v___y_1045_ = v___y_1181_;
v___y_1046_ = v___y_1182_;
v___y_1047_ = v___y_1183_;
v___y_1048_ = v___y_1184_;
goto v___jp_1042_;
}
}
v___jp_1233_:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
lean_inc(v_declName_979_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_declName_979_);
v___x_1242_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4(v_a_1240_, v___x_1241_);
lean_dec_ref_known(v___x_1241_, 1);
if (v___x_1242_ == 0)
{
v___y_1178_ = v___y_1234_;
v___y_1179_ = v___y_1235_;
v___y_1180_ = v___y_1237_;
v___y_1181_ = v_a_1240_;
v___y_1182_ = v___y_1238_;
v___y_1183_ = v___y_1236_;
v___y_1184_ = v___y_1239_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1240_);
lean_dec(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___f_978_);
v___x_1243_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1244_ = l_Lean_MessageData_ofConstName(v_declName_979_, v___x_991_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1247_, v___y_1236_, v___y_1239_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
v___jp_1257_:
{
if (lean_obj_tag(v___y_1258_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_box(0);
v___y_1234_ = v___y_1258_;
v___y_1235_ = v_since_x3f_1261_;
v___y_1236_ = v___y_1262_;
v___y_1237_ = v___y_1259_;
v___y_1238_ = v___y_1260_;
v___y_1239_ = v___y_1263_;
v_a_1240_ = v___x_1264_;
goto v___jp_1233_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_val_1265_ = lean_ctor_get(v___y_1258_, 0);
v___x_1266_ = lean_box(0);
lean_inc(v_val_1265_);
v___x_1267_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_1265_, v___x_1266_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1268_);
v___y_1234_ = v___y_1258_;
v___y_1235_ = v_since_x3f_1261_;
v___y_1236_ = v___y_1262_;
v___y_1237_ = v___y_1259_;
v___y_1238_ = v___y_1260_;
v___y_1239_ = v___y_1263_;
v_a_1240_ = v___x_1269_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v___y_1258_, 1);
lean_dec(v_since_x3f_1261_);
lean_dec(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v_a_1270_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1267_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1267_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
v___jp_1278_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_unsigned_to_nat(4u);
v___x_1286_ = l_Lean_Syntax_getArg(v_stx_980_, v___x_1285_);
lean_dec(v_stx_980_);
v___x_1287_ = l_Lean_Syntax_isNone(v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1286_);
v___x_1289_ = l_Lean_Syntax_matchesNull(v___x_1286_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v___x_1286_);
lean_dec(v_typeChanged_x3f_1282_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___x_1290_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1291_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1290_, v___y_1283_, v___y_1284_);
return v___x_1291_;
}
else
{
lean_object* v_since_x3f_1292_; lean_object* v___x_1293_; 
v_since_x3f_1292_ = l_Lean_Syntax_getArg(v___x_1286_, v___y_1281_);
lean_dec(v___x_1286_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_since_x3f_1292_);
v___y_1258_ = v___y_1279_;
v___y_1259_ = v_typeChanged_x3f_1282_;
v___y_1260_ = v___y_1280_;
v_since_x3f_1261_ = v___x_1293_;
v___y_1262_ = v___y_1283_;
v___y_1263_ = v___y_1284_;
goto v___jp_1257_;
}
}
else
{
lean_object* v___x_1294_; 
lean_dec(v___x_1286_);
v___x_1294_ = lean_box(0);
v___y_1258_ = v___y_1279_;
v___y_1259_ = v_typeChanged_x3f_1282_;
v___y_1260_ = v___y_1280_;
v_since_x3f_1261_ = v___x_1294_;
v___y_1262_ = v___y_1283_;
v___y_1263_ = v___y_1284_;
goto v___jp_1257_;
}
}
v___jp_1295_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_unsigned_to_nat(3u);
v___x_1301_ = l_Lean_Syntax_getArg(v_stx_980_, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_isNone(v___x_1301_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; 
lean_inc(v___x_1301_);
v___x_1303_ = l_Lean_Syntax_matchesNull(v___x_1301_, v___x_1103_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v___x_1301_);
lean_dec(v_text_x3f_1297_);
lean_dec(v___y_1296_);
lean_dec(v_stx_980_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___x_1304_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1305_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1304_, v___y_1298_, v___y_1299_);
return v___x_1305_;
}
else
{
lean_object* v_typeChanged_x3f_1306_; lean_object* v___x_1307_; 
v_typeChanged_x3f_1306_ = l_Lean_Syntax_getArg(v___x_1301_, v___x_1102_);
lean_dec(v___x_1301_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_typeChanged_x3f_1306_);
v___y_1279_ = v___y_1296_;
v___y_1280_ = v_text_x3f_1297_;
v___y_1281_ = v___x_1300_;
v_typeChanged_x3f_1282_ = v___x_1307_;
v___y_1283_ = v___y_1298_;
v___y_1284_ = v___y_1299_;
goto v___jp_1278_;
}
}
else
{
lean_object* v___x_1308_; 
lean_dec(v___x_1301_);
v___x_1308_ = lean_box(0);
v___y_1279_ = v___y_1296_;
v___y_1280_ = v_text_x3f_1297_;
v___y_1281_ = v___x_1300_;
v_typeChanged_x3f_1282_ = v___x_1308_;
v___y_1283_ = v___y_1298_;
v___y_1284_ = v___y_1299_;
goto v___jp_1278_;
}
}
v___jp_1309_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(2u);
v___x_1314_ = l_Lean_Syntax_getArg(v_stx_980_, v___x_1313_);
v___x_1315_ = l_Lean_Syntax_isNone(v___x_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
lean_inc(v___x_1314_);
v___x_1316_ = l_Lean_Syntax_matchesNull(v___x_1314_, v___x_1103_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v___x_1314_);
lean_dec(v_id_x3f_1310_);
lean_dec(v_stx_980_);
lean_dec(v_declName_979_);
lean_dec_ref(v___f_978_);
v___x_1317_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1318_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1317_, v___y_1311_, v___y_1312_);
return v___x_1318_;
}
else
{
lean_object* v_text_x3f_1319_; lean_object* v___x_1320_; 
v_text_x3f_1319_ = l_Lean_Syntax_getArg(v___x_1314_, v___x_1102_);
lean_dec(v___x_1314_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_text_x3f_1319_);
v___y_1296_ = v_id_x3f_1310_;
v_text_x3f_1297_ = v___x_1320_;
v___y_1298_ = v___y_1311_;
v___y_1299_ = v___y_1312_;
goto v___jp_1295_;
}
}
else
{
lean_object* v___x_1321_; 
lean_dec(v___x_1314_);
v___x_1321_ = lean_box(0);
v___y_1296_ = v_id_x3f_1310_;
v_text_x3f_1297_ = v___x_1321_;
v___y_1298_ = v___y_1311_;
v___y_1299_ = v___y_1312_;
goto v___jp_1295_;
}
}
}
v___jp_984_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v___y_987_);
lean_ctor_set(v___x_988_, 1, v___y_985_);
lean_ctor_set(v___x_988_, 2, v___y_986_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
v___jp_992_:
{
if (lean_obj_tag(v___y_994_) == 0)
{
if (v___x_991_ == 0)
{
v___y_985_ = v___y_993_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
goto v___jp_984_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_999_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_998_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_dec_ref_known(v___x_999_, 1);
v___y_985_ = v___y_993_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
goto v___jp_984_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v___y_995_);
lean_dec(v___y_993_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
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
else
{
v___y_985_ = v___y_993_;
v___y_986_ = v___y_994_;
v___y_987_ = v___y_995_;
goto v___jp_984_;
}
}
v___jp_1008_:
{
if (lean_obj_tag(v___y_1009_) == 0)
{
if (v___x_991_ == 0)
{
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1010_;
goto v___jp_992_;
}
else
{
if (lean_obj_tag(v___y_1012_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1016_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_1015_, v___y_1011_, v___y_1010_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref_known(v___x_1016_, 1);
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1010_;
goto v___jp_992_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v___y_1014_);
lean_dec(v___y_1013_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1010_;
goto v___jp_992_;
}
}
}
else
{
lean_dec_ref_known(v___y_1009_, 1);
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1011_;
v___y_997_ = v___y_1010_;
goto v___jp_992_;
}
}
v___jp_1025_:
{
if (lean_obj_tag(v___y_1029_) == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(0);
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1027_;
v___y_1011_ = v___y_1028_;
v___y_1012_ = v___y_1031_;
v___y_1013_ = v___y_1030_;
v___y_1014_ = v___x_1032_;
goto v___jp_1008_;
}
else
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_val_1033_ = lean_ctor_get(v___y_1029_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___y_1029_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v___y_1029_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v___y_1029_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = l_Lean_TSyntax_getString(v_val_1033_);
lean_dec(v_val_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
v___y_1009_ = v___y_1026_;
v___y_1010_ = v___y_1027_;
v___y_1011_ = v___y_1028_;
v___y_1012_ = v___y_1031_;
v___y_1013_ = v___y_1030_;
v___y_1014_ = v___x_1039_;
goto v___jp_1008_;
}
}
}
}
v___jp_1042_:
{
if (lean_obj_tag(v___y_1046_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(0);
v___y_1026_ = v___y_1043_;
v___y_1027_ = v___y_1048_;
v___y_1028_ = v___y_1047_;
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1045_;
v___y_1031_ = v___x_1049_;
goto v___jp_1025_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_val_1050_ = lean_ctor_get(v___y_1046_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___y_1046_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1052_ = v___y_1046_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v___y_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = l_Lean_TSyntax_getString(v_val_1050_);
lean_dec(v_val_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
v___y_1026_ = v___y_1043_;
v___y_1027_ = v___y_1048_;
v___y_1028_ = v___y_1047_;
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1045_;
v___y_1031_ = v___x_1056_;
goto v___jp_1025_;
}
}
}
}
v___jp_1059_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1069_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1070_ = l_Lean_ConstantInfo_type(v___y_1063_);
lean_dec_ref(v___y_1063_);
v___x_1071_ = l_Lean_indentExpr(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1069_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_ConstantInfo_type(v___y_1062_);
lean_dec_ref(v___y_1062_);
v___x_1076_ = l_Lean_indentExpr(v___x_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1074_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_hint_1066_);
v___x_1081_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_1080_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_dec_ref_known(v___x_1081_, 1);
v___y_1043_ = v___y_1060_;
v___y_1044_ = v___y_1061_;
v___y_1045_ = v___y_1064_;
v___y_1046_ = v___y_1065_;
v___y_1047_ = v___y_1067_;
v___y_1048_ = v___y_1068_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec(v___y_1061_);
lean_dec(v___y_1060_);
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___y_1060_ = v___y_1091_;
v___y_1061_ = v___y_1093_;
v___y_1062_ = v___y_1094_;
v___y_1063_ = v___y_1095_;
v___y_1064_ = v___y_1097_;
v___y_1065_ = v___y_1098_;
v_hint_1066_ = v___x_1099_;
v___y_1067_ = v___y_1092_;
v___y_1068_ = v___y_1096_;
goto v___jp_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v___f_1332_, lean_object* v_declName_1333_, lean_object* v_stx_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v___x_1330_, v___x_1331_, v___f_1332_, v_declName_1333_, v_stx_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(uint8_t v___x_1339_, lean_object* v_env_1340_, lean_object* v_n_1341_, lean_object* v_x_1342_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Environment_contains(v_env_1340_, v_n_1341_, v___x_1339_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v___x_1344_, lean_object* v_env_1345_, lean_object* v_n_1346_, lean_object* v_x_1347_){
_start:
{
uint8_t v___x_18237__boxed_1348_; uint8_t v_res_1349_; lean_object* v_r_1350_; 
v___x_18237__boxed_1348_ = lean_unbox(v___x_1344_);
v_res_1349_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v___x_18237__boxed_1348_, v_env_1345_, v_n_1346_, v_x_1347_);
lean_dec_ref(v_x_1347_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1381_ = l_Lean_registerParametricAttribute___redArg(v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_();
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1384_, lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v_msg_1385_, v___y_1386_, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0(v_00_u03b1_1390_, v_msg_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1396_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8(v_o_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_1406_, lean_object* v_m_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_1407_, v_a_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_1410_, lean_object* v_m_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_1410_, v_m_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_m_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_1415_, v_x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_00_u03b2_1418_, v_x_1419_, v_x_1420_);
lean_dec_ref(v_x_1420_);
lean_dec_ref(v_x_1419_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1423_, lean_object* v_m_1424_, lean_object* v_query_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_m_1424_, v_query_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_query_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_00_u03b2_1427_, v_m_1428_, v_query_1429_);
lean_dec(v_query_1429_);
lean_dec_ref(v_m_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, size_t v_x_1433_, lean_object* v_x_1434_){
_start:
{
uint8_t v___x_1435_; 
v___x_1435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_1432_, v_x_1433_, v_x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
size_t v_x_18373__boxed_1440_; uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_x_18373__boxed_1440_ = lean_unbox_usize(v_x_1438_);
lean_dec(v_x_1438_);
v_res_1441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(v_00_u03b2_1436_, v_x_1437_, v_x_18373__boxed_1440_, v_x_1439_);
lean_dec_ref(v_x_1439_);
lean_dec_ref(v_x_1437_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1443_, lean_object* v_m_1444_, lean_object* v_query_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___redArg(v_m_1444_, v_query_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_m_1448_, lean_object* v_query_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16(v_00_u03b2_1447_, v_m_1448_, v_query_1449_);
lean_dec(v_query_1449_);
lean_dec_ref(v_m_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1451_, lean_object* v_keys_1452_, lean_object* v_vals_1453_, lean_object* v_heq_1454_, lean_object* v_i_1455_, lean_object* v_k_1456_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_1452_, v_i_1455_, v_k_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03b2_1458_, lean_object* v_keys_1459_, lean_object* v_vals_1460_, lean_object* v_heq_1461_, lean_object* v_i_1462_, lean_object* v_k_1463_){
_start:
{
uint8_t v_res_1464_; lean_object* v_r_1465_; 
v_res_1464_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(v_00_u03b2_1458_, v_keys_1459_, v_vals_1460_, v_heq_1461_, v_i_1462_, v_k_1463_);
lean_dec_ref(v_k_1463_);
lean_dec_ref(v_vals_1460_);
lean_dec_ref(v_keys_1459_);
v_r_1465_ = lean_box(v_res_1464_);
return v_r_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18(lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_query_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___redArg(v_m_1467_, v_query_1468_, v_x_1469_, v_x_1470_, v_x_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18___boxed(lean_object* v_00_u03b2_1474_, lean_object* v_m_1475_, lean_object* v_query_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__16_spec__18(v_00_u03b2_1474_, v_m_1475_, v_query_1476_, v_x_1477_, v_x_1478_, v_x_1479_, v_x_1480_);
lean_dec(v_query_1476_);
lean_dec_ref(v_m_1475_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_1482_, lean_object* v_entry_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_env_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = l_Lean_Linter_deprecatedAttr;
v___x_1489_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1488_, v_env_1487_, v_declName_1482_, v_entry_1483_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_inst_1486_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1499_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 3);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = l_Lean_MessageData_ofFormat(v___x_1495_);
v___x_1497_ = l_Lean_throwError___redArg(v_inst_1484_, v_inst_1485_, v___x_1496_);
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_inst_1485_);
lean_dec_ref(v_inst_1484_);
v_a_1500_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1501_ = l_Lean_setEnv___redArg(v_inst_1486_, v_a_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_declName_1505_, lean_object* v_entry_1506_){
_start:
{
lean_object* v_toBind_1507_; lean_object* v_getEnv_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; 
v_toBind_1507_ = lean_ctor_get(v_inst_1502_, 1);
lean_inc(v_toBind_1507_);
v_getEnv_1508_ = lean_ctor_get(v_inst_1503_, 0);
lean_inc(v_getEnv_1508_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1509_, 0, v_declName_1505_);
lean_closure_set(v___f_1509_, 1, v_entry_1506_);
lean_closure_set(v___f_1509_, 2, v_inst_1502_);
lean_closure_set(v___f_1509_, 3, v_inst_1504_);
lean_closure_set(v___f_1509_, 4, v_inst_1503_);
v___x_1510_ = lean_apply_4(v_toBind_1507_, lean_box(0), lean_box(0), v_getEnv_1508_, v___f_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_declName_1515_, lean_object* v_entry_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Linter_setDeprecated___redArg(v_inst_1512_, v_inst_1513_, v_inst_1514_, v_declName_1515_, v_entry_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_1518_, lean_object* v_declName_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1521_ = l_Lean_Linter_deprecatedAttr;
v___x_1522_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1520_, v___x_1521_, v_env_1518_, v_declName_1519_);
if (lean_obj_tag(v___x_1522_) == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = 1;
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_1525_, lean_object* v_declName_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Lean_Linter_isDeprecated(v_env_1525_, v_declName_1526_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1531_ = lean_name_eq(v_x_1529_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_1532_);
lean_dec(v_x_1532_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_1536_){
_start:
{
lean_object* v___f_1537_; uint8_t v___x_1538_; 
v___f_1537_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_1538_ = l_Lean_MessageData_hasTag(v___f_1537_, v_msg_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Lean_MessageData_isDeprecationWarning(v_msg_1539_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_1542_, lean_object* v_declName_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1545_ = l_Lean_Linter_deprecatedAttr;
v___x_1546_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1544_, v___x_1545_, v_env_1542_, v_declName_1543_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_box(0);
return v___x_1547_;
}
else
{
lean_object* v_val_1548_; lean_object* v_newName_x3f_1549_; 
v_val_1548_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1546_, 1);
v_newName_x3f_1549_ = lean_ctor_get(v_val_1548_, 0);
lean_inc(v_newName_x3f_1549_);
lean_dec(v_val_1548_);
return v_newName_x3f_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(lean_object* v___x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1550_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed(lean_object* v___x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(v___x_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_1564_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_box(0);
return v___x_1565_;
}
else
{
lean_object* v_head_1566_; lean_object* v_tail_1567_; lean_object* v_fst_1568_; uint8_t v___x_1569_; 
v_head_1566_ = lean_ctor_get(v_x_1564_, 0);
v_tail_1567_ = lean_ctor_get(v_x_1564_, 1);
v_fst_1568_ = lean_ctor_get(v_head_1566_, 0);
v___x_1569_ = l_Lean_isPrivateName(v_fst_1568_);
if (v___x_1569_ == 0)
{
v_x_1564_ = v_tail_1567_;
goto _start;
}
else
{
lean_object* v___x_1571_; 
lean_inc(v_head_1566_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_head_1566_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_1572_);
lean_dec(v_x_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(lean_object* v_msgData_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v_env_1581_; lean_object* v___x_1582_; lean_object* v_mctx_1583_; lean_object* v_lctx_1584_; lean_object* v_options_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1580_ = lean_st_ref_get(v___y_1578_);
v_env_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_env_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = lean_st_ref_get(v___y_1576_);
v_mctx_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc_ref(v_mctx_1583_);
lean_dec(v___x_1582_);
v_lctx_1584_ = lean_ctor_get(v___y_1575_, 2);
v_options_1585_ = lean_ctor_get(v___y_1577_, 2);
lean_inc_ref(v_options_1585_);
lean_inc_ref(v_lctx_1584_);
v___x_1586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1586_, 0, v_env_1581_);
lean_ctor_set(v___x_1586_, 1, v_mctx_1583_);
lean_ctor_set(v___x_1586_, 2, v_lctx_1584_);
lean_ctor_set(v___x_1586_, 3, v_options_1585_);
v___x_1587_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_msgData_1574_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19___boxed(lean_object* v_msgData_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v_msgData_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(lean_object* v_ref_1598_, lean_object* v_msgData_1599_, uint8_t v_severity_1600_, uint8_t v_isSilent_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_a_1608_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1647_; lean_object* v___y_1648_; uint8_t v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1671_; lean_object* v___y_1672_; uint8_t v___y_1673_; uint8_t v___y_1674_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; uint8_t v___x_1693_; lean_object* v___y_1695_; uint8_t v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; uint8_t v___y_1700_; uint8_t v___y_1701_; uint8_t v___y_1703_; uint8_t v___x_1718_; 
v___x_1693_ = 2;
v___x_1718_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1600_, v___x_1693_);
if (v___x_1718_ == 0)
{
v___y_1703_ = v___x_1718_;
goto v___jp_1702_;
}
else
{
uint8_t v___x_1719_; 
lean_inc_ref(v_msgData_1599_);
v___x_1719_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1599_);
v___y_1703_ = v___x_1719_;
goto v___jp_1702_;
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1608_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
v___jp_1611_:
{
lean_object* v___x_1621_; lean_object* v_currNamespace_1622_; lean_object* v_openDecls_1623_; lean_object* v_env_1624_; lean_object* v_nextMacroScope_1625_; lean_object* v_ngen_1626_; lean_object* v_auxDeclNGen_1627_; lean_object* v_traceState_1628_; lean_object* v_cache_1629_; lean_object* v_messages_1630_; lean_object* v_infoState_1631_; lean_object* v_snapshotTasks_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1645_; 
v___x_1621_ = lean_st_ref_take(v___y_1620_);
v_currNamespace_1622_ = lean_ctor_get(v___y_1619_, 6);
v_openDecls_1623_ = lean_ctor_get(v___y_1619_, 7);
v_env_1624_ = lean_ctor_get(v___x_1621_, 0);
v_nextMacroScope_1625_ = lean_ctor_get(v___x_1621_, 1);
v_ngen_1626_ = lean_ctor_get(v___x_1621_, 2);
v_auxDeclNGen_1627_ = lean_ctor_get(v___x_1621_, 3);
v_traceState_1628_ = lean_ctor_get(v___x_1621_, 4);
v_cache_1629_ = lean_ctor_get(v___x_1621_, 5);
v_messages_1630_ = lean_ctor_get(v___x_1621_, 6);
v_infoState_1631_ = lean_ctor_get(v___x_1621_, 7);
v_snapshotTasks_1632_ = lean_ctor_get(v___x_1621_, 8);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1634_ = v___x_1621_;
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_snapshotTasks_1632_);
lean_inc(v_infoState_1631_);
lean_inc(v_messages_1630_);
lean_inc(v_cache_1629_);
lean_inc(v_traceState_1628_);
lean_inc(v_auxDeclNGen_1627_);
lean_inc(v_ngen_1626_);
lean_inc(v_nextMacroScope_1625_);
lean_inc(v_env_1624_);
lean_dec(v___x_1621_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_inc(v_openDecls_1623_);
lean_inc(v_currNamespace_1622_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_currNamespace_1622_);
lean_ctor_set(v___x_1636_, 1, v_openDecls_1623_);
v___x_1637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___y_1618_);
lean_inc_ref(v___y_1617_);
lean_inc_ref(v___y_1613_);
v___x_1638_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1638_, 0, v___y_1613_);
lean_ctor_set(v___x_1638_, 1, v___y_1615_);
lean_ctor_set(v___x_1638_, 2, v___y_1612_);
lean_ctor_set(v___x_1638_, 3, v___y_1617_);
lean_ctor_set(v___x_1638_, 4, v___x_1637_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*5, v___y_1614_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*5 + 1, v___y_1616_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*5 + 2, v_isSilent_1601_);
v___x_1639_ = l_Lean_MessageLog_add(v___x_1638_, v_messages_1630_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 6, v___x_1639_);
v___x_1641_ = v___x_1634_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_env_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1627_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_traceState_1628_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_cache_1629_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_infoState_1631_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_snapshotTasks_1632_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_put(v___y_1620_, v___x_1641_);
v___x_1643_ = lean_box(0);
v_a_1608_ = v___x_1643_;
goto v___jp_1607_;
}
}
}
v___jp_1646_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1669_; 
v___x_1655_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1599_);
v___x_1656_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_1655_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_inc_ref_n(v___y_1653_, 2);
v___x_1661_ = l_Lean_FileMap_toPosition(v___y_1653_, v___y_1651_);
lean_dec(v___y_1651_);
v___x_1662_ = l_Lean_FileMap_toPosition(v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_1652_ == 0)
{
lean_dec_ref(v___y_1647_);
v___y_1612_ = v___x_1664_;
v___y_1613_ = v___y_1648_;
v___y_1614_ = v___y_1649_;
v___y_1615_ = v___x_1661_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___x_1665_;
v___y_1618_ = v_a_1657_;
v___y_1619_ = v___y_1604_;
v___y_1620_ = v___y_1605_;
goto v___jp_1611_;
}
else
{
uint8_t v___x_1666_; 
lean_inc(v_a_1657_);
v___x_1666_ = l_Lean_MessageData_hasTag(v___y_1647_, v_a_1657_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v___x_1664_);
lean_dec_ref(v___x_1661_);
lean_dec(v_a_1657_);
v___x_1667_ = lean_box(0);
v_a_1608_ = v___x_1667_;
goto v___jp_1607_;
}
else
{
v___y_1612_ = v___x_1664_;
v___y_1613_ = v___y_1648_;
v___y_1614_ = v___y_1649_;
v___y_1615_ = v___x_1661_;
v___y_1616_ = v___y_1650_;
v___y_1617_ = v___x_1665_;
v___y_1618_ = v_a_1657_;
v___y_1619_ = v___y_1604_;
v___y_1620_ = v___y_1605_;
goto v___jp_1611_;
}
}
}
}
}
v___jp_1670_:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Syntax_getTailPos_x3f(v___y_1675_, v___y_1673_);
lean_dec(v___y_1675_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_inc(v___y_1678_);
v___y_1647_ = v___y_1671_;
v___y_1648_ = v___y_1672_;
v___y_1649_ = v___y_1673_;
v___y_1650_ = v___y_1674_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1676_;
v___y_1653_ = v___y_1677_;
v___y_1654_ = v___y_1678_;
goto v___jp_1646_;
}
else
{
lean_object* v_val_1680_; 
v_val_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1647_ = v___y_1671_;
v___y_1648_ = v___y_1672_;
v___y_1649_ = v___y_1673_;
v___y_1650_ = v___y_1674_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1676_;
v___y_1653_ = v___y_1677_;
v___y_1654_ = v_val_1680_;
goto v___jp_1646_;
}
}
v___jp_1681_:
{
lean_object* v_ref_1689_; lean_object* v___x_1690_; 
v_ref_1689_ = l_Lean_replaceRef(v_ref_1598_, v___y_1687_);
v___x_1690_ = l_Lean_Syntax_getPos_x3f(v_ref_1689_, v___y_1684_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_unsigned_to_nat(0u);
v___y_1671_ = v___y_1682_;
v___y_1672_ = v___y_1683_;
v___y_1673_ = v___y_1684_;
v___y_1674_ = v___y_1688_;
v___y_1675_ = v_ref_1689_;
v___y_1676_ = v___y_1685_;
v___y_1677_ = v___y_1686_;
v___y_1678_ = v___x_1691_;
goto v___jp_1670_;
}
else
{
lean_object* v_val_1692_; 
v_val_1692_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1690_, 1);
v___y_1671_ = v___y_1682_;
v___y_1672_ = v___y_1683_;
v___y_1673_ = v___y_1684_;
v___y_1674_ = v___y_1688_;
v___y_1675_ = v_ref_1689_;
v___y_1676_ = v___y_1685_;
v___y_1677_ = v___y_1686_;
v___y_1678_ = v_val_1692_;
goto v___jp_1670_;
}
}
v___jp_1694_:
{
if (v___y_1701_ == 0)
{
v___y_1682_ = v___y_1698_;
v___y_1683_ = v___y_1695_;
v___y_1684_ = v___y_1700_;
v___y_1685_ = v___y_1696_;
v___y_1686_ = v___y_1697_;
v___y_1687_ = v___y_1699_;
v___y_1688_ = v_severity_1600_;
goto v___jp_1681_;
}
else
{
v___y_1682_ = v___y_1698_;
v___y_1683_ = v___y_1695_;
v___y_1684_ = v___y_1700_;
v___y_1685_ = v___y_1696_;
v___y_1686_ = v___y_1697_;
v___y_1687_ = v___y_1699_;
v___y_1688_ = v___x_1693_;
goto v___jp_1681_;
}
}
v___jp_1702_:
{
if (v___y_1703_ == 0)
{
lean_object* v_fileName_1704_; lean_object* v_fileMap_1705_; lean_object* v_options_1706_; lean_object* v_ref_1707_; uint8_t v_suppressElabErrors_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; uint8_t v___x_1712_; uint8_t v___x_1713_; 
v_fileName_1704_ = lean_ctor_get(v___y_1604_, 0);
v_fileMap_1705_ = lean_ctor_get(v___y_1604_, 1);
v_options_1706_ = lean_ctor_get(v___y_1604_, 2);
v_ref_1707_ = lean_ctor_get(v___y_1604_, 5);
v_suppressElabErrors_1708_ = lean_ctor_get_uint8(v___y_1604_, sizeof(void*)*14 + 1);
v___x_1709_ = lean_box(v___y_1703_);
v___x_1710_ = lean_box(v_suppressElabErrors_1708_);
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1711_, 0, v___x_1709_);
lean_closure_set(v___f_1711_, 1, v___x_1710_);
v___x_1712_ = 1;
v___x_1713_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1600_, v___x_1712_);
if (v___x_1713_ == 0)
{
v___y_1695_ = v_fileName_1704_;
v___y_1696_ = v_suppressElabErrors_1708_;
v___y_1697_ = v_fileMap_1705_;
v___y_1698_ = v___f_1711_;
v___y_1699_ = v_ref_1707_;
v___y_1700_ = v___y_1703_;
v___y_1701_ = v___x_1713_;
goto v___jp_1694_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = l_Lean_warningAsError;
v___x_1715_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_1706_, v___x_1714_);
v___y_1695_ = v_fileName_1704_;
v___y_1696_ = v_suppressElabErrors_1708_;
v___y_1697_ = v_fileMap_1705_;
v___y_1698_ = v___f_1711_;
v___y_1699_ = v_ref_1707_;
v___y_1700_ = v___y_1703_;
v___y_1701_ = v___x_1715_;
goto v___jp_1694_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v_msgData_1599_);
v___x_1716_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___boxed(lean_object* v_ref_1720_, lean_object* v_msgData_1721_, lean_object* v_severity_1722_, lean_object* v_isSilent_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_severity_boxed_1729_; uint8_t v_isSilent_boxed_1730_; lean_object* v_res_1731_; 
v_severity_boxed_1729_ = lean_unbox(v_severity_1722_);
v_isSilent_boxed_1730_ = lean_unbox(v_isSilent_1723_);
v_res_1731_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1720_, v_msgData_1721_, v_severity_boxed_1729_, v_isSilent_boxed_1730_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v_ref_1720_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(lean_object* v_msgData_1732_, uint8_t v_severity_1733_, uint8_t v_isSilent_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_ref_1740_; lean_object* v___x_1741_; 
v_ref_1740_ = lean_ctor_get(v___y_1737_, 5);
v___x_1741_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1740_, v_msgData_1732_, v_severity_1733_, v_isSilent_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32___boxed(lean_object* v_msgData_1742_, lean_object* v_severity_1743_, lean_object* v_isSilent_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
uint8_t v_severity_boxed_1750_; uint8_t v_isSilent_boxed_1751_; lean_object* v_res_1752_; 
v_severity_boxed_1750_ = lean_unbox(v_severity_1743_);
v_isSilent_boxed_1751_ = lean_unbox(v_isSilent_1744_);
v_res_1752_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1742_, v_severity_boxed_1750_, v_isSilent_boxed_1751_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(lean_object* v_msgData_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = 1;
v___x_1760_ = 0;
v___x_1761_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1753_, v___x_1759_, v___x_1760_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31___boxed(lean_object* v_msgData_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v_msgData_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(lean_object* v_opt_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_options_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_options_1772_ = lean_ctor_get(v___y_1770_, 2);
v___x_1773_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_1772_, v_opt_1769_);
v___x_1774_ = lean_box(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg___boxed(lean_object* v_opt_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_1777_, v___y_1778_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_opt_1777_);
return v_res_1780_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(lean_object* v_id_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v_env_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1817_; 
v___x_1793_ = lean_st_ref_get(v___y_1791_);
v_env_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc_ref(v_env_1794_);
lean_dec(v___x_1793_);
v___x_1795_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1796_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v___x_1795_, v___y_1790_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v_isExporting_1806_; 
v_isExporting_1806_ = lean_ctor_get_uint8(v_env_1794_, sizeof(void*)*8);
lean_dec_ref(v_env_1794_);
if (v_isExporting_1806_ == 0)
{
lean_dec(v_a_1797_);
lean_dec(v_id_1787_);
goto v___jp_1801_;
}
else
{
lean_object* v_val_1807_; uint8_t v___x_1808_; 
v_val_1807_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_val_1807_);
lean_dec(v_a_1797_);
v___x_1808_ = l_Lean_isPrivateName(v_id_1787_);
if (v___x_1808_ == 0)
{
lean_dec(v_val_1807_);
lean_dec(v_id_1787_);
goto v___jp_1801_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_unbox(v_val_1807_);
lean_dec(v_val_1807_);
if (v___x_1809_ == 0)
{
lean_dec(v_id_1787_);
goto v___jp_1801_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_del_object(v___x_1799_);
v___x_1810_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_1811_ = 0;
v___x_1812_ = l_Lean_MessageData_ofConstName(v_id_1787_, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1810_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v___x_1815_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1816_;
}
}
}
v___jp_1801_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___boxed(lean_object* v_id_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_id_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(lean_object* v_id_1825_, uint8_t v_enableLog_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; lean_object* v_env_1833_; lean_object* v_options_1834_; lean_object* v_currNamespace_1835_; lean_object* v_openDecls_1836_; lean_object* v___x_1837_; lean_object* v_env_1838_; lean_object* v_res_1839_; 
v___x_1832_ = lean_st_ref_get(v___y_1830_);
v_env_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_ref(v_env_1833_);
lean_dec(v___x_1832_);
v_options_1834_ = lean_ctor_get(v___y_1829_, 2);
v_currNamespace_1835_ = lean_ctor_get(v___y_1829_, 6);
v_openDecls_1836_ = lean_ctor_get(v___y_1829_, 7);
v___x_1837_ = lean_st_ref_get(v___y_1830_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_env_1838_);
lean_dec(v___x_1837_);
lean_inc(v_openDecls_1836_);
lean_inc(v_currNamespace_1835_);
v_res_1839_ = l_Lean_ResolveName_resolveGlobalName(v_env_1833_, v_options_1834_, v_currNamespace_1835_, v_openDecls_1836_, v_id_1825_);
if (v_enableLog_1826_ == 0)
{
lean_dec_ref(v_env_1838_);
goto v___jp_1840_;
}
else
{
uint8_t v_isExporting_1843_; 
v_isExporting_1843_ = lean_ctor_get_uint8(v_env_1838_, sizeof(void*)*8);
lean_dec_ref(v_env_1838_);
if (v_isExporting_1843_ == 0)
{
goto v___jp_1840_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_1839_);
if (lean_obj_tag(v___x_1844_) == 1)
{
lean_object* v_val_1845_; lean_object* v_fst_1846_; lean_object* v___x_1847_; 
v_val_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_fst_1846_ = lean_ctor_get(v_val_1845_, 0);
lean_inc(v_fst_1846_);
lean_dec(v_val_1845_);
v___x_1847_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_fst_1846_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
if (lean_obj_tag(v_a_1848_) == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec(v_res_1839_);
v___x_1852_ = lean_box(0);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_dec_ref_known(v_a_1848_, 1);
lean_del_object(v___x_1850_);
goto v___jp_1840_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_res_1839_);
v_a_1857_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1847_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1847_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec(v___x_1844_);
goto v___jp_1840_;
}
}
}
v___jp_1840_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_res_1839_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24___boxed(lean_object* v_id_1865_, lean_object* v_enableLog_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v_enableLog_boxed_1872_; lean_object* v_res_1873_; 
v_enableLog_boxed_1872_ = lean_unbox(v_enableLog_1866_);
v_res_1873_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v_id_1865_, v_enableLog_boxed_1872_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(lean_object* v_n_u2080_1878_, lean_object* v_filter_1879_, lean_object* v_view_x3f_1880_, lean_object* v_n_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1957_; 
if (lean_obj_tag(v_view_x3f_1880_) == 1)
{
lean_object* v_val_1984_; lean_object* v_imported_1985_; lean_object* v_ctx_1986_; lean_object* v_scopes_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_val_1984_ = lean_ctor_get(v_view_x3f_1880_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v_view_x3f_1880_, 1);
v_imported_1985_ = lean_ctor_get(v_val_1984_, 1);
v_ctx_1986_ = lean_ctor_get(v_val_1984_, 2);
v_scopes_1987_ = lean_ctor_get(v_val_1984_, 3);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_val_1984_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_val_1984_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v_val_1984_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_scopes_1987_);
lean_inc(v_ctx_1986_);
lean_inc(v_imported_1985_);
lean_dec(v_val_1984_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v_n_1881_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_n_1881_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_imported_1985_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_ctx_1986_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_scopes_1987_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_MacroScopesView_review(v___x_1992_);
v___y_1957_ = v___x_1993_;
goto v___jp_1956_;
}
}
}
else
{
lean_dec(v_view_x3f_1880_);
v___y_1957_ = v_n_1881_;
goto v___jp_1956_;
}
v___jp_1887_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
v___jp_1890_:
{
lean_object* v___x_1893_; 
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1893_ = lean_apply_5(v___y_1892_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, lean_box(0));
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1913_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1913_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1913_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
if (lean_obj_tag(v_a_1894_) == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_dec(v___y_1891_);
v___x_1898_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v_a_1894_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_a_1894_, 0);
lean_dec(v_unused_1912_);
v___x_1903_ = v_a_1894_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_dec(v_a_1894_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___y_1891_);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___y_1891_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1906_);
v___x_1908_ = v___x_1896_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___y_1891_);
v_a_1914_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1893_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1893_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
v___jp_1922_:
{
lean_object* v___x_1925_; 
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1925_ = lean_apply_5(v___y_1924_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, lean_box(0));
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1947_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
if (lean_obj_tag(v_a_1926_) == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
lean_dec(v___y_1923_);
lean_dec_ref(v_filter_1879_);
v___x_1930_ = lean_box(0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
else
{
lean_object* v___x_1934_; 
lean_dec_ref_known(v_a_1926_, 1);
lean_del_object(v___x_1928_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1923_);
v___x_1934_ = lean_apply_6(v_filter_1879_, v___y_1923_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, lean_box(0));
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; uint8_t v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___f_1937_; 
v___f_1937_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1891_ = v___y_1923_;
v___y_1892_ = v___f_1937_;
goto v___jp_1890_;
}
else
{
lean_object* v___f_1938_; 
v___f_1938_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1891_ = v___y_1923_;
v___y_1892_ = v___f_1938_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v___y_1923_);
v_a_1939_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1934_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1934_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v___y_1923_);
lean_dec_ref(v_filter_1879_);
v_a_1948_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1925_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1925_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v___jp_1956_:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = 0;
lean_inc(v___y_1957_);
v___x_1959_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v___y_1957_, v___x_1958_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1975_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1975_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1975_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
if (lean_obj_tag(v_a_1960_) == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_dec(v___y_1957_);
lean_dec_ref(v_filter_1879_);
v___x_1964_ = lean_box(0);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v_val_1968_; 
lean_del_object(v___x_1962_);
v_val_1968_ = lean_ctor_get(v_a_1960_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_a_1960_, 1);
if (lean_obj_tag(v_val_1968_) == 1)
{
lean_object* v_head_1969_; lean_object* v_tail_1970_; 
v_head_1969_ = lean_ctor_get(v_val_1968_, 0);
lean_inc(v_head_1969_);
v_tail_1970_ = lean_ctor_get(v_val_1968_, 1);
lean_inc(v_tail_1970_);
lean_dec_ref_known(v_val_1968_, 2);
if (lean_obj_tag(v_tail_1970_) == 0)
{
lean_object* v_fst_1971_; uint8_t v___x_1972_; 
v_fst_1971_ = lean_ctor_get(v_head_1969_, 0);
lean_inc(v_fst_1971_);
lean_dec(v_head_1969_);
v___x_1972_ = lean_name_eq(v_fst_1971_, v_n_u2080_1878_);
lean_dec(v_fst_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___f_1973_; 
v___f_1973_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1923_ = v___y_1957_;
v___y_1924_ = v___f_1973_;
goto v___jp_1922_;
}
else
{
lean_object* v___f_1974_; 
v___f_1974_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1923_ = v___y_1957_;
v___y_1924_ = v___f_1974_;
goto v___jp_1922_;
}
}
else
{
lean_dec(v_tail_1970_);
lean_dec(v_head_1969_);
lean_dec(v___y_1957_);
lean_dec_ref(v_filter_1879_);
goto v___jp_1887_;
}
}
else
{
lean_dec(v_val_1968_);
lean_dec(v___y_1957_);
lean_dec_ref(v_filter_1879_);
goto v___jp_1887_;
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v___y_1957_);
lean_dec_ref(v_filter_1879_);
v_a_1976_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1959_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1959_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___boxed(lean_object* v_n_u2080_1997_, lean_object* v_filter_1998_, lean_object* v_view_x3f_1999_, lean_object* v_n_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_1997_, v_filter_1998_, v_view_x3f_1999_, v_n_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v_n_u2080_1997_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(lean_object* v_n_u2080_2007_, lean_object* v_filter_2008_, lean_object* v_view_x3f_2009_, lean_object* v_as_x27_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
if (lean_obj_tag(v_as_x27_2010_) == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v_view_x3f_2009_);
lean_dec_ref(v_filter_2008_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_2011_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
else
{
lean_object* v_head_2019_; lean_object* v_tail_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2059_; 
v_head_2019_ = lean_ctor_get(v_as_x27_2010_, 0);
v_tail_2020_ = lean_ctor_get(v_as_x27_2010_, 1);
v_snd_2021_ = lean_ctor_get(v_b_2011_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_b_2011_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_b_2011_, 0);
lean_dec(v_unused_2060_);
v___x_2023_ = v_b_2011_;
v_isShared_2024_ = v_isSharedCheck_2059_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_dec(v_b_2011_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2059_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Name_appendCore(v_head_2019_, v_snd_2021_);
lean_inc(v___x_2025_);
lean_inc(v_view_x3f_2009_);
lean_inc_ref(v_filter_2008_);
v___x_2026_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2007_, v_filter_2008_, v_view_x3f_2009_, v___x_2025_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2050_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2050_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
if (lean_obj_tag(v_a_2027_) == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
lean_del_object(v___x_2029_);
v___x_2031_ = lean_box(0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2025_);
lean_ctor_set(v___x_2023_, 0, v___x_2031_);
v___x_2033_ = v___x_2023_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2025_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v_as_x27_2010_ = v_tail_2020_;
v_b_2011_ = v___x_2033_;
goto _start;
}
}
else
{
lean_object* v___x_2037_; 
lean_dec(v_view_x3f_2009_);
lean_dec_ref(v_filter_2008_);
lean_inc_ref(v_a_2027_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2025_);
lean_ctor_set(v___x_2023_, 0, v_a_2027_);
v___x_2037_ = v___x_2023_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2027_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2025_);
v___x_2037_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v_a_2027_, 0);
lean_dec(v_unused_2048_);
v___x_2039_ = v_a_2027_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v_a_2027_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2037_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2042_);
v___x_2044_ = v___x_2029_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v___x_2025_);
lean_del_object(v___x_2023_);
lean_dec(v_view_x3f_2009_);
lean_dec_ref(v_filter_2008_);
v_a_2051_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2026_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2026_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg___boxed(lean_object* v_n_u2080_2061_, lean_object* v_filter_2062_, lean_object* v_view_x3f_2063_, lean_object* v_as_x27_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_2061_, v_filter_2062_, v_view_x3f_2063_, v_as_x27_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v_as_x27_2064_);
lean_dec(v_n_u2080_2061_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(lean_object* v_n_u2080_2075_, lean_object* v_filter_2076_, lean_object* v_view_x3f_2077_, lean_object* v_n_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___y_2085_; uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_Name_hasMacroScopes(v_n_2078_);
if (v___x_2126_ == 0)
{
lean_object* v___f_2127_; 
v___f_2127_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_2085_ = v___f_2127_;
goto v___jp_2084_;
}
else
{
lean_object* v___f_2128_; 
v___f_2128_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_2085_ = v___f_2128_;
goto v___jp_2084_;
}
v___jp_2084_:
{
lean_object* v___x_2086_; 
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
v___x_2086_ = lean_apply_5(v___y_2085_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, lean_box(0));
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2117_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
if (lean_obj_tag(v_a_2087_) == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec(v_n_2078_);
lean_dec(v_view_x3f_2077_);
lean_dec_ref(v_filter_2076_);
v___x_2091_ = lean_box(0);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec_ref_known(v_a_2087_, 1);
lean_del_object(v___x_2089_);
v___x_2095_ = l_Lean_privateToUserName(v_n_2078_);
v___x_2096_ = l_Lean_Name_componentsRev(v___x_2095_);
v___x_2097_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0));
v___x_2098_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_2075_, v_filter_2076_, v_view_x3f_2077_, v___x_2096_, v___x_2097_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___x_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2108_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_val_2103_; lean_object* v_fst_2104_; lean_object* v___x_2106_; 
v_val_2103_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_val_2103_);
lean_dec(v_a_2099_);
v_fst_2104_ = lean_ctor_get(v_val_2103_, 0);
lean_inc(v_fst_2104_);
lean_dec(v_val_2103_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v_fst_2104_);
v___x_2106_ = v___x_2101_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_fst_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2098_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2098_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_n_2078_);
lean_dec(v_view_x3f_2077_);
lean_dec_ref(v_filter_2076_);
v_a_2118_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2086_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2086_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___boxed(lean_object* v_n_u2080_2129_, lean_object* v_filter_2130_, lean_object* v_view_x3f_2131_, lean_object* v_n_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2129_, v_filter_2130_, v_view_x3f_2131_, v_n_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v_n_u2080_2129_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(lean_object* v_n_u2080_2139_, lean_object* v_filter_2140_, lean_object* v_as_2141_, lean_object* v_i_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_as_2141_);
v___x_2149_ = lean_nat_dec_lt(v_i_2142_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec(v_i_2142_);
lean_dec_ref(v_filter_2140_);
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_array_fget_borrowed(v_as_2141_, v_i_2142_);
lean_inc(v___x_2153_);
lean_inc_ref(v_filter_2140_);
v___x_2154_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2139_, v_filter_2140_, v___x_2152_, v___x_2153_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
if (lean_obj_tag(v_a_2155_) == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_i_2142_, v___x_2156_);
lean_dec(v_i_2142_);
v_i_2142_ = v___x_2157_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_2155_, 1);
lean_dec(v_i_2142_);
lean_dec_ref(v_filter_2140_);
return v___x_2154_;
}
}
else
{
lean_dec(v_i_2142_);
lean_dec_ref(v_filter_2140_);
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14___boxed(lean_object* v_n_u2080_2159_, lean_object* v_filter_2160_, lean_object* v_as_2161_, lean_object* v_i_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2159_, v_filter_2160_, v_as_2161_, v_i_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v_as_2161_);
lean_dec(v_n_u2080_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(lean_object* v_n_u2081_2169_, lean_object* v_as_2170_, size_t v_i_2171_, size_t v_stop_2172_, lean_object* v_b_2173_){
_start:
{
lean_object* v___y_2175_; uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_eq(v_i_2171_, v_stop_2172_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2180_ = lean_array_uget_borrowed(v_as_2170_, v_i_2171_);
v___x_2181_ = l_Lean_Name_getPrefix(v___x_2180_);
v___x_2182_ = l_Lean_Name_getPrefix(v_n_u2081_2169_);
v___x_2183_ = l_Lean_Name_isPrefixOf(v___x_2181_, v___x_2182_);
lean_dec(v___x_2182_);
lean_dec(v___x_2181_);
if (v___x_2183_ == 0)
{
v___y_2175_ = v_b_2173_;
goto v___jp_2174_;
}
else
{
lean_object* v___x_2184_; 
lean_inc(v___x_2180_);
v___x_2184_ = lean_array_push(v_b_2173_, v___x_2180_);
v___y_2175_ = v___x_2184_;
goto v___jp_2174_;
}
}
else
{
return v_b_2173_;
}
v___jp_2174_:
{
size_t v___x_2176_; size_t v___x_2177_; 
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = lean_usize_add(v_i_2171_, v___x_2176_);
v_i_2171_ = v___x_2177_;
v_b_2173_ = v___y_2175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15___boxed(lean_object* v_n_u2081_2185_, lean_object* v_as_2186_, lean_object* v_i_2187_, lean_object* v_stop_2188_, lean_object* v_b_2189_){
_start:
{
size_t v_i_boxed_2190_; size_t v_stop_boxed_2191_; lean_object* v_res_2192_; 
v_i_boxed_2190_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_stop_boxed_2191_ = lean_unbox_usize(v_stop_2188_);
lean_dec(v_stop_2188_);
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2185_, v_as_2186_, v_i_boxed_2190_, v_stop_boxed_2191_, v_b_2189_);
lean_dec_ref(v_as_2186_);
lean_dec(v_n_u2081_2185_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(lean_object* v_n_u2080_2195_, uint8_t v_fullNames_2196_, uint8_t v_allowHorizAliases_2197_, lean_object* v_filter_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_view_2204_; lean_object* v_name_2205_; lean_object* v_n_u2081_2206_; 
lean_inc(v_n_u2080_2195_);
v_view_2204_ = l_Lean_extractMacroScopes(v_n_u2080_2195_);
v_name_2205_ = lean_ctor_get(v_view_2204_, 0);
lean_inc(v_name_2205_);
v_n_u2081_2206_ = l_Lean_privateToUserName(v_name_2205_);
if (v_fullNames_2196_ == 0)
{
lean_object* v___x_2207_; lean_object* v_aliases_2209_; lean_object* v_env_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2207_ = lean_st_ref_get(v___y_2202_);
v_env_2224_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2224_);
lean_dec(v___x_2207_);
lean_inc(v_n_u2080_2195_);
v___x_2225_ = l_Lean_getRevAliases(v_env_2224_, v_n_u2080_2195_);
v___x_2226_ = lean_array_mk(v___x_2225_);
if (v_allowHorizAliases_2197_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_array_get_size(v___x_2226_);
v___x_2229_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0));
v___x_2230_ = lean_nat_dec_lt(v___x_2227_, v___x_2228_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_2226_);
v_aliases_2209_ = v___x_2229_;
goto v___jp_2208_;
}
else
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_nat_dec_le(v___x_2228_, v___x_2228_);
if (v___x_2231_ == 0)
{
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_2226_);
v_aliases_2209_ = v___x_2229_;
goto v___jp_2208_;
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2228_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2206_, v___x_2226_, v___x_2232_, v___x_2233_, v___x_2229_);
lean_dec_ref(v___x_2226_);
v_aliases_2209_ = v___x_2234_;
goto v___jp_2208_;
}
}
else
{
size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = lean_usize_of_nat(v___x_2228_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2206_, v___x_2226_, v___x_2235_, v___x_2236_, v___x_2229_);
lean_dec_ref(v___x_2226_);
v_aliases_2209_ = v___x_2237_;
goto v___jp_2208_;
}
}
}
else
{
v_aliases_2209_ = v___x_2226_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_2198_);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2195_, v_filter_2198_, v_aliases_2209_, v___x_2210_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec_ref(v_aliases_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
if (lean_obj_tag(v_a_2212_) == 0)
{
lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v___x_2211_, 0);
lean_dec(v_unused_2223_);
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
else
{
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 1);
lean_ctor_set(v___x_2214_, 0, v_view_2204_);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_view_2204_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = l_Lean_rootNamespace;
v___x_2219_ = l_Lean_Name_append(v___x_2218_, v_n_u2081_2206_);
v___x_2220_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2195_, v_filter_2198_, v___x_2217_, v___x_2219_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v_n_u2080_2195_);
return v___x_2220_;
}
}
}
else
{
lean_dec_ref_known(v_a_2212_, 1);
lean_dec(v_n_u2081_2206_);
lean_dec_ref(v_view_2204_);
lean_dec_ref(v_filter_2198_);
lean_dec(v_n_u2080_2195_);
return v___x_2211_;
}
}
else
{
lean_dec(v_n_u2081_2206_);
lean_dec_ref(v_view_2204_);
lean_dec_ref(v_filter_2198_);
lean_dec(v_n_u2080_2195_);
return v___x_2211_;
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_view_2204_);
lean_inc(v_n_u2081_2206_);
lean_inc_ref(v___x_2238_);
lean_inc_ref(v_filter_2198_);
v___x_2239_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2195_, v_filter_2198_, v___x_2238_, v_n_u2081_2206_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
if (lean_obj_tag(v_a_2240_) == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = l_Lean_rootNamespace;
v___x_2242_ = l_Lean_Name_append(v___x_2241_, v_n_u2081_2206_);
v___x_2243_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2195_, v_filter_2198_, v___x_2238_, v___x_2242_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v_n_u2080_2195_);
return v___x_2243_;
}
else
{
lean_dec_ref_known(v_a_2240_, 1);
lean_dec_ref_known(v___x_2238_, 1);
lean_dec(v_n_u2081_2206_);
lean_dec_ref(v_filter_2198_);
lean_dec(v_n_u2080_2195_);
return v___x_2239_;
}
}
else
{
lean_dec_ref_known(v___x_2238_, 1);
lean_dec(v_n_u2081_2206_);
lean_dec_ref(v_filter_2198_);
lean_dec(v_n_u2080_2195_);
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___boxed(lean_object* v_n_u2080_2244_, lean_object* v_fullNames_2245_, lean_object* v_allowHorizAliases_2246_, lean_object* v_filter_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v_fullNames_boxed_2253_; uint8_t v_allowHorizAliases_boxed_2254_; lean_object* v_res_2255_; 
v_fullNames_boxed_2253_ = lean_unbox(v_fullNames_2245_);
v_allowHorizAliases_boxed_2254_ = lean_unbox(v_allowHorizAliases_2246_);
v_res_2255_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2244_, v_fullNames_boxed_2253_, v_allowHorizAliases_boxed_2254_, v_filter_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
if (lean_obj_tag(v_a_2256_) == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = l_List_reverse___redArg(v_a_2257_);
return v___x_2258_;
}
else
{
lean_object* v_head_2259_; lean_object* v_tail_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2271_; 
v_head_2259_ = lean_ctor_get(v_a_2256_, 0);
v_tail_2260_ = lean_ctor_get(v_a_2256_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2256_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2262_ = v_a_2256_;
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_tail_2260_);
lean_inc(v_head_2259_);
lean_dec(v_a_2256_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_snd_2264_; uint8_t v___x_2265_; 
v_snd_2264_ = lean_ctor_get(v_head_2259_, 1);
v___x_2265_ = l_List_isEmpty___redArg(v_snd_2264_);
if (v___x_2265_ == 0)
{
lean_del_object(v___x_2262_);
lean_dec(v_head_2259_);
v_a_2256_ = v_tail_2260_;
goto _start;
}
else
{
lean_object* v___x_2268_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v_a_2257_);
v___x_2268_ = v___x_2262_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_head_2259_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2257_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
v_a_2256_ = v_tail_2260_;
v_a_2257_ = v___x_2268_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_opt_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_options_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_options_2275_ = lean_ctor_get(v___y_2273_, 2);
v___x_2276_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_2275_, v_opt_2272_);
v___x_2277_ = lean_box(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_opt_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_2279_, v___y_2280_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_opt_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(lean_object* v_ref_2283_, lean_object* v_msgData_2284_, uint8_t v_severity_2285_, uint8_t v_isSilent_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; uint8_t v___y_2298_; uint8_t v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2329_; uint8_t v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; uint8_t v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2354_; lean_object* v___y_2355_; uint8_t v___y_2356_; uint8_t v___y_2357_; lean_object* v___y_2358_; uint8_t v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; uint8_t v___x_2376_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2383_; uint8_t v___y_2384_; uint8_t v___y_2386_; uint8_t v___x_2401_; 
v___x_2376_ = 2;
v___x_2401_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2285_, v___x_2376_);
if (v___x_2401_ == 0)
{
v___y_2386_ = v___x_2401_;
goto v___jp_2385_;
}
else
{
uint8_t v___x_2402_; 
lean_inc_ref(v_msgData_2284_);
v___x_2402_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2284_);
v___y_2386_ = v___x_2402_;
goto v___jp_2385_;
}
v___jp_2292_:
{
lean_object* v___x_2302_; lean_object* v_currNamespace_2303_; lean_object* v_openDecls_2304_; lean_object* v_env_2305_; lean_object* v_nextMacroScope_2306_; lean_object* v_ngen_2307_; lean_object* v_auxDeclNGen_2308_; lean_object* v_traceState_2309_; lean_object* v_cache_2310_; lean_object* v_messages_2311_; lean_object* v_infoState_2312_; lean_object* v_snapshotTasks_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2327_; 
v___x_2302_ = lean_st_ref_take(v___y_2301_);
v_currNamespace_2303_ = lean_ctor_get(v___y_2300_, 6);
v_openDecls_2304_ = lean_ctor_get(v___y_2300_, 7);
v_env_2305_ = lean_ctor_get(v___x_2302_, 0);
v_nextMacroScope_2306_ = lean_ctor_get(v___x_2302_, 1);
v_ngen_2307_ = lean_ctor_get(v___x_2302_, 2);
v_auxDeclNGen_2308_ = lean_ctor_get(v___x_2302_, 3);
v_traceState_2309_ = lean_ctor_get(v___x_2302_, 4);
v_cache_2310_ = lean_ctor_get(v___x_2302_, 5);
v_messages_2311_ = lean_ctor_get(v___x_2302_, 6);
v_infoState_2312_ = lean_ctor_get(v___x_2302_, 7);
v_snapshotTasks_2313_ = lean_ctor_get(v___x_2302_, 8);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2315_ = v___x_2302_;
v_isShared_2316_ = v_isSharedCheck_2327_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snapshotTasks_2313_);
lean_inc(v_infoState_2312_);
lean_inc(v_messages_2311_);
lean_inc(v_cache_2310_);
lean_inc(v_traceState_2309_);
lean_inc(v_auxDeclNGen_2308_);
lean_inc(v_ngen_2307_);
lean_inc(v_nextMacroScope_2306_);
lean_inc(v_env_2305_);
lean_dec(v___x_2302_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2327_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_inc(v_openDecls_2304_);
lean_inc(v_currNamespace_2303_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_currNamespace_2303_);
lean_ctor_set(v___x_2317_, 1, v_openDecls_2304_);
v___x_2318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___y_2293_);
lean_inc_ref(v___y_2297_);
lean_inc_ref(v___y_2294_);
v___x_2319_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2319_, 0, v___y_2294_);
lean_ctor_set(v___x_2319_, 1, v___y_2295_);
lean_ctor_set(v___x_2319_, 2, v___y_2296_);
lean_ctor_set(v___x_2319_, 3, v___y_2297_);
lean_ctor_set(v___x_2319_, 4, v___x_2318_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*5, v___y_2298_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*5 + 1, v___y_2299_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*5 + 2, v_isSilent_2286_);
v___x_2320_ = l_Lean_MessageLog_add(v___x_2319_, v_messages_2311_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 6, v___x_2320_);
v___x_2322_ = v___x_2315_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_env_2305_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_nextMacroScope_2306_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_ngen_2307_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_auxDeclNGen_2308_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_traceState_2309_);
lean_ctor_set(v_reuseFailAlloc_2326_, 5, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2326_, 6, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 7, v_infoState_2312_);
lean_ctor_set(v_reuseFailAlloc_2326_, 8, v_snapshotTasks_2313_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = lean_st_ref_put(v___y_2301_, v___x_2322_);
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
}
v___jp_2328_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2352_; 
v___x_2337_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2284_);
v___x_2338_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_2337_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc_ref_n(v___y_2335_, 2);
v___x_2343_ = l_Lean_FileMap_toPosition(v___y_2335_, v___y_2334_);
lean_dec(v___y_2334_);
v___x_2344_ = l_Lean_FileMap_toPosition(v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_2332_ == 0)
{
lean_del_object(v___x_2341_);
lean_dec_ref(v___y_2329_);
v___y_2293_ = v_a_2339_;
v___y_2294_ = v___y_2331_;
v___y_2295_ = v___x_2343_;
v___y_2296_ = v___x_2345_;
v___y_2297_ = v___x_2346_;
v___y_2298_ = v___y_2333_;
v___y_2299_ = v___y_2330_;
v___y_2300_ = v___y_2289_;
v___y_2301_ = v___y_2290_;
goto v___jp_2292_;
}
else
{
uint8_t v___x_2347_; 
lean_inc(v_a_2339_);
v___x_2347_ = l_Lean_MessageData_hasTag(v___y_2329_, v_a_2339_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec_ref_known(v___x_2345_, 1);
lean_dec_ref(v___x_2343_);
lean_dec(v_a_2339_);
v___x_2348_ = lean_box(0);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2348_);
v___x_2350_ = v___x_2341_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
else
{
lean_del_object(v___x_2341_);
v___y_2293_ = v_a_2339_;
v___y_2294_ = v___y_2331_;
v___y_2295_ = v___x_2343_;
v___y_2296_ = v___x_2345_;
v___y_2297_ = v___x_2346_;
v___y_2298_ = v___y_2333_;
v___y_2299_ = v___y_2330_;
v___y_2300_ = v___y_2289_;
v___y_2301_ = v___y_2290_;
goto v___jp_2292_;
}
}
}
}
v___jp_2353_:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Syntax_getTailPos_x3f(v___y_2358_, v___y_2357_);
lean_dec(v___y_2358_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_inc(v___y_2361_);
v___y_2329_ = v___y_2354_;
v___y_2330_ = v___y_2359_;
v___y_2331_ = v___y_2355_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2357_;
v___y_2334_ = v___y_2361_;
v___y_2335_ = v___y_2360_;
v___y_2336_ = v___y_2361_;
goto v___jp_2328_;
}
else
{
lean_object* v_val_2363_; 
v_val_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_val_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___y_2329_ = v___y_2354_;
v___y_2330_ = v___y_2359_;
v___y_2331_ = v___y_2355_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2357_;
v___y_2334_ = v___y_2361_;
v___y_2335_ = v___y_2360_;
v___y_2336_ = v_val_2363_;
goto v___jp_2328_;
}
}
v___jp_2364_:
{
lean_object* v_ref_2372_; lean_object* v___x_2373_; 
v_ref_2372_ = l_Lean_replaceRef(v_ref_2283_, v___y_2366_);
v___x_2373_ = l_Lean_Syntax_getPos_x3f(v_ref_2372_, v___y_2369_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_unsigned_to_nat(0u);
v___y_2354_ = v___y_2365_;
v___y_2355_ = v___y_2367_;
v___y_2356_ = v___y_2368_;
v___y_2357_ = v___y_2369_;
v___y_2358_ = v_ref_2372_;
v___y_2359_ = v___y_2371_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v___x_2374_;
goto v___jp_2353_;
}
else
{
lean_object* v_val_2375_; 
v_val_2375_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2375_);
lean_dec_ref_known(v___x_2373_, 1);
v___y_2354_ = v___y_2365_;
v___y_2355_ = v___y_2367_;
v___y_2356_ = v___y_2368_;
v___y_2357_ = v___y_2369_;
v___y_2358_ = v_ref_2372_;
v___y_2359_ = v___y_2371_;
v___y_2360_ = v___y_2370_;
v___y_2361_ = v_val_2375_;
goto v___jp_2353_;
}
}
v___jp_2377_:
{
if (v___y_2384_ == 0)
{
v___y_2365_ = v___y_2378_;
v___y_2366_ = v___y_2379_;
v___y_2367_ = v___y_2380_;
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2382_;
v___y_2371_ = v_severity_2285_;
goto v___jp_2364_;
}
else
{
v___y_2365_ = v___y_2378_;
v___y_2366_ = v___y_2379_;
v___y_2367_ = v___y_2380_;
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2382_;
v___y_2371_ = v___x_2376_;
goto v___jp_2364_;
}
}
v___jp_2385_:
{
if (v___y_2386_ == 0)
{
lean_object* v_fileName_2387_; lean_object* v_fileMap_2388_; lean_object* v_options_2389_; lean_object* v_ref_2390_; uint8_t v_suppressElabErrors_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; uint8_t v___x_2395_; uint8_t v___x_2396_; 
v_fileName_2387_ = lean_ctor_get(v___y_2289_, 0);
v_fileMap_2388_ = lean_ctor_get(v___y_2289_, 1);
v_options_2389_ = lean_ctor_get(v___y_2289_, 2);
v_ref_2390_ = lean_ctor_get(v___y_2289_, 5);
v_suppressElabErrors_2391_ = lean_ctor_get_uint8(v___y_2289_, sizeof(void*)*14 + 1);
v___x_2392_ = lean_box(v___y_2386_);
v___x_2393_ = lean_box(v_suppressElabErrors_2391_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2394_, 0, v___x_2392_);
lean_closure_set(v___f_2394_, 1, v___x_2393_);
v___x_2395_ = 1;
v___x_2396_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2285_, v___x_2395_);
if (v___x_2396_ == 0)
{
v___y_2378_ = v___f_2394_;
v___y_2379_ = v_ref_2390_;
v___y_2380_ = v_fileName_2387_;
v___y_2381_ = v_suppressElabErrors_2391_;
v___y_2382_ = v_fileMap_2388_;
v___y_2383_ = v___y_2386_;
v___y_2384_ = v___x_2396_;
goto v___jp_2377_;
}
else
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = l_Lean_warningAsError;
v___x_2398_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_2389_, v___x_2397_);
v___y_2378_ = v___f_2394_;
v___y_2379_ = v_ref_2390_;
v___y_2380_ = v_fileName_2387_;
v___y_2381_ = v_suppressElabErrors_2391_;
v___y_2382_ = v_fileMap_2388_;
v___y_2383_ = v___y_2386_;
v___y_2384_ = v___x_2398_;
goto v___jp_2377_;
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v_msgData_2284_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_ref_2403_, lean_object* v_msgData_2404_, lean_object* v_severity_2405_, lean_object* v_isSilent_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v_severity_boxed_2412_; uint8_t v_isSilent_boxed_2413_; lean_object* v_res_2414_; 
v_severity_boxed_2412_ = lean_unbox(v_severity_2405_);
v_isSilent_boxed_2413_ = lean_unbox(v_isSilent_2406_);
v_res_2414_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2403_, v_msgData_2404_, v_severity_boxed_2412_, v_isSilent_boxed_2413_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_ref_2403_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(lean_object* v_msgData_2415_, uint8_t v_severity_2416_, uint8_t v_isSilent_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_ref_2423_; lean_object* v___x_2424_; 
v_ref_2423_ = lean_ctor_get(v___y_2420_, 5);
v___x_2424_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2423_, v_msgData_2415_, v_severity_2416_, v_isSilent_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_2425_, lean_object* v_severity_2426_, lean_object* v_isSilent_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v_severity_boxed_2433_; uint8_t v_isSilent_boxed_2434_; lean_object* v_res_2435_; 
v_severity_boxed_2433_ = lean_unbox(v_severity_2426_);
v_isSilent_boxed_2434_ = lean_unbox(v_isSilent_2427_);
v_res_2435_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2425_, v_severity_boxed_2433_, v_isSilent_boxed_2434_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(lean_object* v_msgData_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = 1;
v___x_2443_ = 0;
v___x_2444_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2436_, v___x_2442_, v___x_2443_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v_msgData_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(lean_object* v_id_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_env_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2481_; 
v___x_2458_ = lean_st_ref_get(v___y_2456_);
v_env_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_env_2459_);
lean_dec(v___x_2458_);
v___x_2460_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_2461_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v___x_2460_, v___y_2455_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2481_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2481_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
uint8_t v_isExporting_2471_; 
v_isExporting_2471_ = lean_ctor_get_uint8(v_env_2459_, sizeof(void*)*8);
lean_dec_ref(v_env_2459_);
if (v_isExporting_2471_ == 0)
{
lean_dec(v_a_2462_);
lean_dec(v_id_2452_);
goto v___jp_2466_;
}
else
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Lean_isPrivateName(v_id_2452_);
if (v___x_2472_ == 0)
{
lean_dec(v_a_2462_);
lean_dec(v_id_2452_);
goto v___jp_2466_;
}
else
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_unbox(v_a_2462_);
lean_dec(v_a_2462_);
if (v___x_2473_ == 0)
{
lean_dec(v_id_2452_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_del_object(v___x_2464_);
v___x_2474_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_2475_ = 0;
v___x_2476_ = l_Lean_MessageData_ofConstName(v_id_2452_, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_2479_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2480_;
}
}
}
v___jp_2466_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2467_);
v___x_2469_ = v___x_2464_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1___boxed(lean_object* v_id_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_id_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_id_2489_, uint8_t v_enableLog_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v_env_2497_; lean_object* v_options_2498_; lean_object* v_currNamespace_2499_; lean_object* v_openDecls_2500_; lean_object* v___x_2501_; lean_object* v_env_2502_; lean_object* v_res_2503_; 
v___x_2496_ = lean_st_ref_get(v___y_2494_);
v_env_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc_ref(v_env_2497_);
lean_dec(v___x_2496_);
v_options_2498_ = lean_ctor_get(v___y_2493_, 2);
v_currNamespace_2499_ = lean_ctor_get(v___y_2493_, 6);
v_openDecls_2500_ = lean_ctor_get(v___y_2493_, 7);
v___x_2501_ = lean_st_ref_get(v___y_2494_);
v_env_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc_ref(v_env_2502_);
lean_dec(v___x_2501_);
lean_inc(v_openDecls_2500_);
lean_inc(v_currNamespace_2499_);
v_res_2503_ = l_Lean_ResolveName_resolveGlobalName(v_env_2497_, v_options_2498_, v_currNamespace_2499_, v_openDecls_2500_, v_id_2489_);
if (v_enableLog_2490_ == 0)
{
lean_object* v___x_2504_; 
lean_dec_ref(v_env_2502_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_res_2503_);
return v___x_2504_;
}
else
{
uint8_t v_isExporting_2505_; 
v_isExporting_2505_ = lean_ctor_get_uint8(v_env_2502_, sizeof(void*)*8);
lean_dec_ref(v_env_2502_);
if (v_isExporting_2505_ == 0)
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_res_2503_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_2503_);
if (lean_obj_tag(v___x_2507_) == 1)
{
lean_object* v_val_2508_; lean_object* v_fst_2509_; lean_object* v___x_2510_; 
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v_fst_2509_ = lean_ctor_get(v_val_2508_, 0);
lean_inc(v_fst_2509_);
lean_dec(v_val_2508_);
v___x_2510_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_fst_2509_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2510_, 0);
lean_dec(v_unused_2518_);
v___x_2512_ = v___x_2510_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v___x_2510_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v_res_2503_);
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_res_2503_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_res_2503_);
v_a_2519_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2510_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2510_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v___x_2527_; 
lean_dec(v___x_2507_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_res_2503_);
return v___x_2527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_id_2528_, lean_object* v_enableLog_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v_enableLog_boxed_2535_; lean_object* v_res_2536_; 
v_enableLog_boxed_2535_ = lean_unbox(v_enableLog_2529_);
v_res_2536_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_id_2528_, v_enableLog_boxed_2535_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(lean_object* v_view_2537_, lean_object* v_findLocalDecl_x3f_2538_, lean_object* v_n_2539_, lean_object* v_projs_2540_, uint8_t v_globalDeclFound_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v_globalDeclFoundNext_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v_imported_2557_; lean_object* v_ctx_2558_; lean_object* v_scopes_2559_; lean_object* v_givenNameView_2560_; uint8_t v___y_2562_; 
v_imported_2557_ = lean_ctor_get(v_view_2537_, 1);
v_ctx_2558_ = lean_ctor_get(v_view_2537_, 2);
v_scopes_2559_ = lean_ctor_get(v_view_2537_, 3);
lean_inc(v_scopes_2559_);
lean_inc(v_ctx_2558_);
lean_inc(v_imported_2557_);
lean_inc(v_n_2539_);
v_givenNameView_2560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2560_, 0, v_n_2539_);
lean_ctor_set(v_givenNameView_2560_, 1, v_imported_2557_);
lean_ctor_set(v_givenNameView_2560_, 2, v_ctx_2558_);
lean_ctor_set(v_givenNameView_2560_, 3, v_scopes_2559_);
if (v_globalDeclFound_2541_ == 0)
{
v___y_2562_ = v_globalDeclFound_2541_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2597_; 
v___x_2597_ = l_List_isEmpty___redArg(v_projs_2540_);
if (v___x_2597_ == 0)
{
v___y_2562_ = v_globalDeclFound_2541_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = 0;
v___y_2562_ = v___x_2598_;
goto v___jp_2561_;
}
}
v___jp_2547_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2549_);
lean_ctor_set(v___x_2555_, 1, v_projs_2540_);
v_n_2539_ = v___y_2548_;
v_projs_2540_ = v___x_2555_;
v_globalDeclFound_2541_ = v_globalDeclFoundNext_2550_;
v___y_2542_ = v___y_2551_;
v___y_2543_ = v___y_2552_;
v___y_2544_ = v___y_2553_;
v___y_2545_ = v___y_2554_;
goto _start;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_box(v___y_2562_);
lean_inc_ref(v_findLocalDecl_x3f_2538_);
lean_inc_ref(v_givenNameView_2560_);
v___x_2564_ = lean_apply_2(v_findLocalDecl_x3f_2538_, v_givenNameView_2560_, v___x_2563_);
if (lean_obj_tag(v___x_2564_) == 0)
{
if (lean_obj_tag(v_n_2539_) == 1)
{
if (v_globalDeclFound_2541_ == 0)
{
lean_object* v_pre_2565_; lean_object* v_str_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_pre_2565_ = lean_ctor_get(v_n_2539_, 0);
lean_inc(v_pre_2565_);
v_str_2566_ = lean_ctor_get(v_n_2539_, 1);
lean_inc_ref(v_str_2566_);
lean_dec_ref_known(v_n_2539_, 2);
v___x_2567_ = l_Lean_MacroScopesView_review(v_givenNameView_2560_);
v___x_2568_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v___x_2567_, v_globalDeclFound_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v_r_2571_; uint8_t v___x_2572_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = lean_box(0);
v_r_2571_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(v_a_2569_, v___x_2570_);
v___x_2572_ = l_List_isEmpty___redArg(v_r_2571_);
lean_dec(v_r_2571_);
if (v___x_2572_ == 0)
{
uint8_t v_globalDeclFoundNext_2573_; 
v_globalDeclFoundNext_2573_ = 1;
v___y_2548_ = v_pre_2565_;
v___y_2549_ = v_str_2566_;
v_globalDeclFoundNext_2550_ = v_globalDeclFoundNext_2573_;
v___y_2551_ = v___y_2542_;
v___y_2552_ = v___y_2543_;
v___y_2553_ = v___y_2544_;
v___y_2554_ = v___y_2545_;
goto v___jp_2547_;
}
else
{
v___y_2548_ = v_pre_2565_;
v___y_2549_ = v_str_2566_;
v_globalDeclFoundNext_2550_ = v_globalDeclFound_2541_;
v___y_2551_ = v___y_2542_;
v___y_2552_ = v___y_2543_;
v___y_2553_ = v___y_2544_;
v___y_2554_ = v___y_2545_;
goto v___jp_2547_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_str_2566_);
lean_dec(v_pre_2565_);
lean_dec(v_projs_2540_);
lean_dec_ref(v_findLocalDecl_x3f_2538_);
v_a_2574_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2568_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2568_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_pre_2582_; lean_object* v_str_2583_; 
lean_dec_ref_known(v_givenNameView_2560_, 4);
v_pre_2582_ = lean_ctor_get(v_n_2539_, 0);
lean_inc(v_pre_2582_);
v_str_2583_ = lean_ctor_get(v_n_2539_, 1);
lean_inc_ref(v_str_2583_);
lean_dec_ref_known(v_n_2539_, 2);
v___y_2548_ = v_pre_2582_;
v___y_2549_ = v_str_2583_;
v_globalDeclFoundNext_2550_ = v_globalDeclFound_2541_;
v___y_2551_ = v___y_2542_;
v___y_2552_ = v___y_2543_;
v___y_2553_ = v___y_2544_;
v___y_2554_ = v___y_2545_;
goto v___jp_2547_;
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec_ref_known(v_givenNameView_2560_, 4);
lean_dec(v_projs_2540_);
lean_dec(v_n_2539_);
lean_dec_ref(v_findLocalDecl_x3f_2538_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref_known(v_givenNameView_2560_, 4);
lean_dec(v_n_2539_);
lean_dec_ref(v_findLocalDecl_x3f_2538_);
v_val_2586_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2588_ = v___x_2564_;
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_val_2586_);
lean_dec(v___x_2564_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2590_ = l_Lean_LocalDecl_toExpr(v_val_2586_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v_projs_2540_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2591_);
v___x_2593_ = v___x_2588_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11___boxed(lean_object* v_view_2599_, lean_object* v_findLocalDecl_x3f_2600_, lean_object* v_n_2601_, lean_object* v_projs_2602_, lean_object* v_globalDeclFound_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
uint8_t v_globalDeclFound_boxed_2609_; lean_object* v_res_2610_; 
v_globalDeclFound_boxed_2609_ = lean_unbox(v_globalDeclFound_2603_);
v_res_2610_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2599_, v_findLocalDecl_x3f_2600_, v_n_2601_, v_projs_2602_, v_globalDeclFound_boxed_2609_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_view_2599_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(lean_object* v_localDecl_2611_, lean_object* v_givenName_2612_){
_start:
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = l_Lean_LocalDecl_userName(v_localDecl_2611_);
v___x_2614_ = lean_name_eq(v___x_2613_, v_givenName_2612_);
lean_dec(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
lean_dec_ref(v_localDecl_2611_);
v___x_2615_ = lean_box(0);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_localDecl_2611_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_localDecl_2617_, lean_object* v_givenName_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_localDecl_2617_, v_givenName_2618_);
lean_dec(v_givenName_2618_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(lean_object* v_t_2620_, lean_object* v_k_2621_){
_start:
{
if (lean_obj_tag(v_t_2620_) == 0)
{
lean_object* v_k_2622_; lean_object* v_v_2623_; lean_object* v_l_2624_; lean_object* v_r_2625_; uint8_t v___x_2626_; 
v_k_2622_ = lean_ctor_get(v_t_2620_, 1);
v_v_2623_ = lean_ctor_get(v_t_2620_, 2);
v_l_2624_ = lean_ctor_get(v_t_2620_, 3);
v_r_2625_ = lean_ctor_get(v_t_2620_, 4);
v___x_2626_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2621_, v_k_2622_);
switch(v___x_2626_)
{
case 0:
{
v_t_2620_ = v_l_2624_;
goto _start;
}
case 1:
{
lean_object* v___x_2628_; 
lean_inc(v_v_2623_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_v_2623_);
return v___x_2628_;
}
default: 
{
v_t_2620_ = v_r_2625_;
goto _start;
}
}
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_box(0);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_t_2631_, lean_object* v_k_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_2631_, v_k_2632_);
lean_dec(v_k_2632_);
lean_dec(v_t_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(lean_object* v_givenName_2634_, uint8_t v_skipAuxDecl_2635_, lean_object* v_auxDeclToFullName_2636_, lean_object* v___x_2637_, lean_object* v_givenNameView_2638_, lean_object* v_as_2639_, lean_object* v_i_2640_){
_start:
{
lean_object* v_zero_2641_; uint8_t v_isZero_2642_; 
v_zero_2641_ = lean_unsigned_to_nat(0u);
v_isZero_2642_ = lean_nat_dec_eq(v_i_2640_, v_zero_2641_);
if (v_isZero_2642_ == 1)
{
lean_object* v___x_2643_; 
lean_dec(v_i_2640_);
lean_dec_ref(v_givenNameView_2638_);
lean_dec(v___x_2637_);
v___x_2643_ = lean_box(0);
return v___x_2643_;
}
else
{
lean_object* v_one_2644_; lean_object* v_n_2645_; lean_object* v___y_2647_; lean_object* v___x_2649_; 
v_one_2644_ = lean_unsigned_to_nat(1u);
v_n_2645_ = lean_nat_sub(v_i_2640_, v_one_2644_);
lean_dec(v_i_2640_);
v___x_2649_ = lean_array_fget_borrowed(v_as_2639_, v_n_2645_);
if (lean_obj_tag(v___x_2649_) == 0)
{
v___y_2647_ = v___x_2649_;
goto v___jp_2646_;
}
else
{
lean_object* v_val_2650_; uint8_t v___x_2651_; 
v_val_2650_ = lean_ctor_get(v___x_2649_, 0);
v___x_2651_ = l_Lean_LocalDecl_isAuxDecl(v_val_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
lean_inc(v_val_2650_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2650_, v_givenName_2634_);
v___y_2647_ = v___x_2652_;
goto v___jp_2646_;
}
else
{
if (v_skipAuxDecl_2635_ == 0)
{
if (v___x_2651_ == 0)
{
v_i_2640_ = v_n_2645_;
goto _start;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = l_Lean_LocalDecl_fvarId(v_val_2650_);
v___x_2655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_auxDeclToFullName_2636_, v___x_2654_);
lean_dec(v___x_2654_);
if (lean_obj_tag(v___x_2655_) == 1)
{
lean_object* v_val_2656_; lean_object* v_fullDeclView_2657_; lean_object* v___y_2659_; lean_object* v_name_2680_; lean_object* v___x_2681_; 
v_val_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v_fullDeclView_2657_ = l_Lean_extractMacroScopes(v_val_2656_);
v_name_2680_ = lean_ctor_get(v_fullDeclView_2657_, 0);
lean_inc_n(v_name_2680_, 2);
v___x_2681_ = l_Lean_privateToUserName_x3f(v_name_2680_);
if (lean_obj_tag(v___x_2681_) == 0)
{
v___y_2659_ = v_name_2680_;
goto v___jp_2658_;
}
else
{
lean_object* v_val_2682_; 
lean_dec(v_name_2680_);
v_val_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___y_2659_ = v_val_2682_;
goto v___jp_2658_;
}
v___jp_2658_:
{
lean_object* v_imported_2660_; lean_object* v_ctx_2661_; lean_object* v_scopes_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2678_; 
v_imported_2660_ = lean_ctor_get(v_fullDeclView_2657_, 1);
v_ctx_2661_ = lean_ctor_get(v_fullDeclView_2657_, 2);
v_scopes_2662_ = lean_ctor_get(v_fullDeclView_2657_, 3);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_fullDeclView_2657_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_fullDeclView_2657_, 0);
lean_dec(v_unused_2679_);
v___x_2664_ = v_fullDeclView_2657_;
v_isShared_2665_ = v_isSharedCheck_2678_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_scopes_2662_);
lean_inc(v_ctx_2661_);
lean_inc(v_imported_2660_);
lean_dec(v_fullDeclView_2657_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2678_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_fullDeclView_2667_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___y_2659_);
v_fullDeclView_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___y_2659_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_imported_2660_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_ctx_2661_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_scopes_2662_);
v_fullDeclView_2667_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v_fullDeclName_2668_; uint8_t v___x_2669_; 
lean_inc_ref(v_fullDeclView_2667_);
v_fullDeclName_2668_ = l_Lean_MacroScopesView_review(v_fullDeclView_2667_);
v___x_2669_ = l_Lean_Name_isPrefixOf(v___x_2637_, v_fullDeclName_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v_fullDeclView_2667_);
lean_inc(v___x_2637_);
lean_inc_ref(v_givenNameView_2638_);
lean_inc(v_val_2650_);
v___x_2670_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2650_, v_givenNameView_2638_, v_fullDeclName_2668_, v___x_2637_);
lean_dec(v_fullDeclName_2668_);
v___y_2647_ = v___x_2670_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2671_; lean_object* v_localDeclNameView_2672_; uint8_t v___x_2673_; 
lean_dec(v_fullDeclName_2668_);
v___x_2671_ = l_Lean_LocalDecl_userName(v_val_2650_);
v_localDeclNameView_2672_ = l_Lean_extractMacroScopes(v___x_2671_);
v___x_2673_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2672_, v_givenNameView_2638_);
lean_dec_ref(v_localDeclNameView_2672_);
if (v___x_2673_ == 0)
{
lean_dec_ref(v_fullDeclView_2667_);
v_i_2640_ = v_n_2645_;
goto _start;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2638_, v_fullDeclView_2667_);
lean_dec_ref(v_fullDeclView_2667_);
if (v___x_2675_ == 0)
{
v_i_2640_ = v_n_2645_;
goto _start;
}
else
{
lean_inc_ref(v___x_2649_);
v___y_2647_ = v___x_2649_;
goto v___jp_2646_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v___x_2655_);
lean_inc(v_val_2650_);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2650_, v_givenName_2634_);
v___y_2647_ = v___x_2683_;
goto v___jp_2646_;
}
}
}
else
{
v_i_2640_ = v_n_2645_;
goto _start;
}
}
}
v___jp_2646_:
{
if (lean_obj_tag(v___y_2647_) == 0)
{
v_i_2640_ = v_n_2645_;
goto _start;
}
else
{
lean_dec(v_n_2645_);
lean_dec_ref(v_givenNameView_2638_);
lean_dec(v___x_2637_);
return v___y_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___boxed(lean_object* v_givenName_2685_, lean_object* v_skipAuxDecl_2686_, lean_object* v_auxDeclToFullName_2687_, lean_object* v___x_2688_, lean_object* v_givenNameView_2689_, lean_object* v_as_2690_, lean_object* v_i_2691_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2692_; lean_object* v_res_2693_; 
v_skipAuxDecl_boxed_2692_ = lean_unbox(v_skipAuxDecl_2686_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2685_, v_skipAuxDecl_boxed_2692_, v_auxDeclToFullName_2687_, v___x_2688_, v_givenNameView_2689_, v_as_2690_, v_i_2691_);
lean_dec_ref(v_as_2690_);
lean_dec(v_auxDeclToFullName_2687_);
lean_dec(v_givenName_2685_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(lean_object* v_givenName_2694_, uint8_t v_skipAuxDecl_2695_, lean_object* v_auxDeclToFullName_2696_, lean_object* v___x_2697_, lean_object* v_givenNameView_2698_, lean_object* v_as_2699_, lean_object* v_i_2700_){
_start:
{
lean_object* v_zero_2701_; uint8_t v_isZero_2702_; 
v_zero_2701_ = lean_unsigned_to_nat(0u);
v_isZero_2702_ = lean_nat_dec_eq(v_i_2700_, v_zero_2701_);
if (v_isZero_2702_ == 1)
{
lean_object* v___x_2703_; 
lean_dec(v_i_2700_);
lean_dec_ref(v_givenNameView_2698_);
lean_dec(v___x_2697_);
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_one_2704_; lean_object* v_n_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_one_2704_ = lean_unsigned_to_nat(1u);
v_n_2705_ = lean_nat_sub(v_i_2700_, v_one_2704_);
lean_dec(v_i_2700_);
v___x_2706_ = lean_array_fget_borrowed(v_as_2699_, v_n_2705_);
lean_inc_ref(v_givenNameView_2698_);
lean_inc(v___x_2697_);
v___x_2707_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2694_, v_skipAuxDecl_2695_, v_auxDeclToFullName_2696_, v___x_2697_, v_givenNameView_2698_, v___x_2706_);
if (lean_obj_tag(v___x_2707_) == 0)
{
v_i_2700_ = v_n_2705_;
goto _start;
}
else
{
lean_dec(v_n_2705_);
lean_dec_ref(v_givenNameView_2698_);
lean_dec(v___x_2697_);
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(lean_object* v_givenName_2709_, uint8_t v_skipAuxDecl_2710_, lean_object* v_auxDeclToFullName_2711_, lean_object* v___x_2712_, lean_object* v_givenNameView_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2714_) == 0)
{
lean_object* v_cs_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_cs_2715_ = lean_ctor_get(v_x_2714_, 0);
v___x_2716_ = lean_array_get_size(v_cs_2715_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2709_, v_skipAuxDecl_2710_, v_auxDeclToFullName_2711_, v___x_2712_, v_givenNameView_2713_, v_cs_2715_, v___x_2716_);
return v___x_2717_;
}
else
{
lean_object* v_vs_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_vs_2718_ = lean_ctor_get(v_x_2714_, 0);
v___x_2719_ = lean_array_get_size(v_vs_2718_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2709_, v_skipAuxDecl_2710_, v_auxDeclToFullName_2711_, v___x_2712_, v_givenNameView_2713_, v_vs_2718_, v___x_2719_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_givenName_2721_, lean_object* v_skipAuxDecl_2722_, lean_object* v_auxDeclToFullName_2723_, lean_object* v___x_2724_, lean_object* v_givenNameView_2725_, lean_object* v_x_2726_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2727_; lean_object* v_res_2728_; 
v_skipAuxDecl_boxed_2727_ = lean_unbox(v_skipAuxDecl_2722_);
v_res_2728_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2721_, v_skipAuxDecl_boxed_2727_, v_auxDeclToFullName_2723_, v___x_2724_, v_givenNameView_2725_, v_x_2726_);
lean_dec_ref(v_x_2726_);
lean_dec(v_auxDeclToFullName_2723_);
lean_dec(v_givenName_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg___boxed(lean_object* v_givenName_2729_, lean_object* v_skipAuxDecl_2730_, lean_object* v_auxDeclToFullName_2731_, lean_object* v___x_2732_, lean_object* v_givenNameView_2733_, lean_object* v_as_2734_, lean_object* v_i_2735_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2736_; lean_object* v_res_2737_; 
v_skipAuxDecl_boxed_2736_ = lean_unbox(v_skipAuxDecl_2730_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2729_, v_skipAuxDecl_boxed_2736_, v_auxDeclToFullName_2731_, v___x_2732_, v_givenNameView_2733_, v_as_2734_, v_i_2735_);
lean_dec_ref(v_as_2734_);
lean_dec(v_auxDeclToFullName_2731_);
lean_dec(v_givenName_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(lean_object* v_givenName_2738_, uint8_t v_skipAuxDecl_2739_, lean_object* v_auxDeclToFullName_2740_, lean_object* v___x_2741_, lean_object* v_givenNameView_2742_, lean_object* v_t_2743_){
_start:
{
lean_object* v_root_2744_; lean_object* v_tail_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_root_2744_ = lean_ctor_get(v_t_2743_, 0);
v_tail_2745_ = lean_ctor_get(v_t_2743_, 1);
v___x_2746_ = lean_array_get_size(v_tail_2745_);
lean_inc_ref(v_givenNameView_2742_);
lean_inc(v___x_2741_);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2738_, v_skipAuxDecl_2739_, v_auxDeclToFullName_2740_, v___x_2741_, v_givenNameView_2742_, v_tail_2745_, v___x_2746_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2738_, v_skipAuxDecl_2739_, v_auxDeclToFullName_2740_, v___x_2741_, v_givenNameView_2742_, v_root_2744_);
return v___x_2748_;
}
else
{
lean_dec_ref(v_givenNameView_2742_);
lean_dec(v___x_2741_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9___boxed(lean_object* v_givenName_2749_, lean_object* v_skipAuxDecl_2750_, lean_object* v_auxDeclToFullName_2751_, lean_object* v___x_2752_, lean_object* v_givenNameView_2753_, lean_object* v_t_2754_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2755_; lean_object* v_res_2756_; 
v_skipAuxDecl_boxed_2755_ = lean_unbox(v_skipAuxDecl_2750_);
v_res_2756_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2749_, v_skipAuxDecl_boxed_2755_, v_auxDeclToFullName_2751_, v___x_2752_, v_givenNameView_2753_, v_t_2754_);
lean_dec_ref(v_t_2754_);
lean_dec(v_auxDeclToFullName_2751_);
lean_dec(v_givenName_2749_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(lean_object* v_localDecl_x3f_2757_, lean_object* v_givenName_2758_, lean_object* v_as_2759_, lean_object* v_i_2760_){
_start:
{
lean_object* v_zero_2761_; uint8_t v_isZero_2762_; 
v_zero_2761_ = lean_unsigned_to_nat(0u);
v_isZero_2762_ = lean_nat_dec_eq(v_i_2760_, v_zero_2761_);
if (v_isZero_2762_ == 1)
{
lean_object* v___x_2763_; 
lean_dec(v_i_2760_);
v___x_2763_ = lean_box(0);
return v___x_2763_;
}
else
{
lean_object* v_one_2764_; lean_object* v_n_2765_; lean_object* v___y_2767_; lean_object* v___x_2769_; 
v_one_2764_ = lean_unsigned_to_nat(1u);
v_n_2765_ = lean_nat_sub(v_i_2760_, v_one_2764_);
lean_dec(v_i_2760_);
v___x_2769_ = lean_array_fget_borrowed(v_as_2759_, v_n_2765_);
if (lean_obj_tag(v___x_2769_) == 0)
{
v___y_2767_ = v___x_2769_;
goto v___jp_2766_;
}
else
{
lean_object* v_val_2770_; uint8_t v___x_2771_; 
v_val_2770_ = lean_ctor_get(v___x_2769_, 0);
v___x_2771_ = l_Lean_LocalDecl_isAuxDecl(v_val_2770_);
if (v___x_2771_ == 0)
{
v___y_2767_ = v_localDecl_x3f_2757_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = l_Lean_LocalDecl_userName(v_val_2770_);
v___x_2773_ = lean_name_eq(v___x_2772_, v_givenName_2758_);
lean_dec(v___x_2772_);
if (v___x_2773_ == 0)
{
v_i_2760_ = v_n_2765_;
goto _start;
}
else
{
v___y_2767_ = v___x_2769_;
goto v___jp_2766_;
}
}
}
v___jp_2766_:
{
if (lean_obj_tag(v___y_2767_) == 0)
{
v_i_2760_ = v_n_2765_;
goto _start;
}
else
{
lean_dec(v_n_2765_);
lean_inc_ref(v___y_2767_);
return v___y_2767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_localDecl_x3f_2775_, lean_object* v_givenName_2776_, lean_object* v_as_2777_, lean_object* v_i_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2775_, v_givenName_2776_, v_as_2777_, v_i_2778_);
lean_dec_ref(v_as_2777_);
lean_dec(v_givenName_2776_);
lean_dec(v_localDecl_x3f_2775_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(lean_object* v_localDecl_x3f_2780_, lean_object* v_givenName_2781_, lean_object* v_as_2782_, lean_object* v_i_2783_){
_start:
{
lean_object* v_zero_2784_; uint8_t v_isZero_2785_; 
v_zero_2784_ = lean_unsigned_to_nat(0u);
v_isZero_2785_ = lean_nat_dec_eq(v_i_2783_, v_zero_2784_);
if (v_isZero_2785_ == 1)
{
lean_object* v___x_2786_; 
lean_dec(v_i_2783_);
v___x_2786_ = lean_box(0);
return v___x_2786_;
}
else
{
lean_object* v_one_2787_; lean_object* v_n_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_one_2787_ = lean_unsigned_to_nat(1u);
v_n_2788_ = lean_nat_sub(v_i_2783_, v_one_2787_);
lean_dec(v_i_2783_);
v___x_2789_ = lean_array_fget_borrowed(v_as_2782_, v_n_2788_);
v___x_2790_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2780_, v_givenName_2781_, v___x_2789_);
if (lean_obj_tag(v___x_2790_) == 0)
{
v_i_2783_ = v_n_2788_;
goto _start;
}
else
{
lean_dec(v_n_2788_);
return v___x_2790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(lean_object* v_localDecl_x3f_2792_, lean_object* v_givenName_2793_, lean_object* v_x_2794_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
lean_object* v_cs_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_cs_2795_ = lean_ctor_get(v_x_2794_, 0);
v___x_2796_ = lean_array_get_size(v_cs_2795_);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2792_, v_givenName_2793_, v_cs_2795_, v___x_2796_);
return v___x_2797_;
}
else
{
lean_object* v_vs_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_vs_2798_ = lean_ctor_get(v_x_2794_, 0);
v___x_2799_ = lean_array_get_size(v_vs_2798_);
v___x_2800_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2792_, v_givenName_2793_, v_vs_2798_, v___x_2799_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15___boxed(lean_object* v_localDecl_x3f_2801_, lean_object* v_givenName_2802_, lean_object* v_x_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2801_, v_givenName_2802_, v_x_2803_);
lean_dec_ref(v_x_2803_);
lean_dec(v_givenName_2802_);
lean_dec(v_localDecl_x3f_2801_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg___boxed(lean_object* v_localDecl_x3f_2805_, lean_object* v_givenName_2806_, lean_object* v_as_2807_, lean_object* v_i_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2805_, v_givenName_2806_, v_as_2807_, v_i_2808_);
lean_dec_ref(v_as_2807_);
lean_dec(v_givenName_2806_);
lean_dec(v_localDecl_x3f_2805_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(lean_object* v_localDecl_x3f_2810_, lean_object* v_givenName_2811_, lean_object* v_t_2812_){
_start:
{
lean_object* v_root_2813_; lean_object* v_tail_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_root_2813_ = lean_ctor_get(v_t_2812_, 0);
v_tail_2814_ = lean_ctor_get(v_t_2812_, 1);
v___x_2815_ = lean_array_get_size(v_tail_2814_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2810_, v_givenName_2811_, v_tail_2814_, v___x_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2810_, v_givenName_2811_, v_root_2813_);
return v___x_2817_;
}
else
{
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10___boxed(lean_object* v_localDecl_x3f_2818_, lean_object* v_givenName_2819_, lean_object* v_t_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2818_, v_givenName_2819_, v_t_2820_);
lean_dec_ref(v_t_2820_);
lean_dec(v_givenName_2819_);
lean_dec(v_localDecl_x3f_2818_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(lean_object* v_auxDeclToFullName_2822_, lean_object* v_currNamespace_2823_, lean_object* v_decls_2824_, lean_object* v_givenNameView_2825_, uint8_t v_skipAuxDecl_2826_){
_start:
{
lean_object* v_givenName_2827_; lean_object* v_localDecl_x3f_2828_; 
lean_inc_ref(v_givenNameView_2825_);
v_givenName_2827_ = l_Lean_MacroScopesView_review(v_givenNameView_2825_);
v_localDecl_x3f_2828_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2827_, v_skipAuxDecl_2826_, v_auxDeclToFullName_2822_, v_currNamespace_2823_, v_givenNameView_2825_, v_decls_2824_);
if (lean_obj_tag(v_localDecl_x3f_2828_) == 0)
{
if (v_skipAuxDecl_2826_ == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2828_, v_givenName_2827_, v_decls_2824_);
lean_dec(v_givenName_2827_);
return v___x_2829_;
}
else
{
lean_dec(v_givenName_2827_);
return v_localDecl_x3f_2828_;
}
}
else
{
lean_dec(v_givenName_2827_);
return v_localDecl_x3f_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_2830_, lean_object* v_currNamespace_2831_, lean_object* v_decls_2832_, lean_object* v_givenNameView_2833_, lean_object* v_skipAuxDecl_2834_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2835_; lean_object* v_res_2836_; 
v_skipAuxDecl_boxed_2835_ = lean_unbox(v_skipAuxDecl_2834_);
v_res_2836_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(v_auxDeclToFullName_2830_, v_currNamespace_2831_, v_decls_2832_, v_givenNameView_2833_, v_skipAuxDecl_boxed_2835_);
lean_dec_ref(v_decls_2832_);
lean_dec(v_auxDeclToFullName_2830_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(lean_object* v_n_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_lctx_2843_; lean_object* v_decls_2844_; lean_object* v_auxDeclToFullName_2845_; lean_object* v_currNamespace_2846_; lean_object* v_view_2847_; lean_object* v_name_2848_; lean_object* v_findLocalDecl_x3f_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v_lctx_2843_ = lean_ctor_get(v___y_2838_, 2);
v_decls_2844_ = lean_ctor_get(v_lctx_2843_, 1);
v_auxDeclToFullName_2845_ = lean_ctor_get(v_lctx_2843_, 2);
v_currNamespace_2846_ = lean_ctor_get(v___y_2840_, 6);
v_view_2847_ = l_Lean_extractMacroScopes(v_n_2837_);
v_name_2848_ = lean_ctor_get(v_view_2847_, 0);
lean_inc(v_name_2848_);
lean_inc_ref(v_decls_2844_);
lean_inc(v_currNamespace_2846_);
lean_inc(v_auxDeclToFullName_2845_);
v_findLocalDecl_x3f_2849_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_2849_, 0, v_auxDeclToFullName_2845_);
lean_closure_set(v_findLocalDecl_x3f_2849_, 1, v_currNamespace_2846_);
lean_closure_set(v_findLocalDecl_x3f_2849_, 2, v_decls_2844_);
v___x_2850_ = lean_box(0);
v___x_2851_ = 0;
v___x_2852_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2847_, v_findLocalDecl_x3f_2849_, v_name_2848_, v___x_2850_, v___x_2851_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec_ref(v_view_2847_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___boxed(lean_object* v_n_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(uint8_t v___x_2860_, lean_object* v_n_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2881_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
if (lean_obj_tag(v_a_2868_) == 0)
{
uint8_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2872_ = 1;
v___x_2873_ = lean_box(v___x_2872_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2873_);
v___x_2875_ = v___x_2870_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_dec_ref_known(v_a_2868_, 1);
v___x_2877_ = lean_box(v___x_2860_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2877_);
v___x_2879_ = v___x_2870_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
v_a_2882_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2867_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2867_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0___boxed(lean_object* v___x_2890_, lean_object* v_n_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
uint8_t v___x_27606__boxed_2897_; lean_object* v_res_2898_; 
v___x_27606__boxed_2897_ = lean_unbox(v___x_2890_);
v_res_2898_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(v___x_27606__boxed_2897_, v_n_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(lean_object* v_n_u2080_2902_, uint8_t v_fullNames_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
uint8_t v___x_2909_; lean_object* v___f_2910_; lean_object* v___x_2911_; 
v___x_2909_ = 0;
v___f_2910_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0));
v___x_2911_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2902_, v_fullNames_2903_, v___x_2909_, v___f_2910_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___boxed(lean_object* v_n_u2080_2912_, lean_object* v_fullNames_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v_fullNames_boxed_2919_; lean_object* v_res_2920_; 
v_fullNames_boxed_2919_ = lean_unbox(v_fullNames_2913_);
v_res_2920_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_n_u2080_2912_, v_fullNames_boxed_2919_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(lean_object* v_x_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2921_) == 0)
{
if (lean_obj_tag(v_x_2922_) == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = 1;
return v___x_2923_;
}
else
{
uint8_t v___x_2924_; 
v___x_2924_ = 0;
return v___x_2924_;
}
}
else
{
if (lean_obj_tag(v_x_2922_) == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = 0;
return v___x_2925_;
}
else
{
lean_object* v_head_2926_; lean_object* v_tail_2927_; lean_object* v_head_2928_; lean_object* v_tail_2929_; uint8_t v___x_2930_; 
v_head_2926_ = lean_ctor_get(v_x_2921_, 0);
v_tail_2927_ = lean_ctor_get(v_x_2921_, 1);
v_head_2928_ = lean_ctor_get(v_x_2922_, 0);
v_tail_2929_ = lean_ctor_get(v_x_2922_, 1);
v___x_2930_ = lean_string_dec_eq(v_head_2926_, v_head_2928_);
if (v___x_2930_ == 0)
{
return v___x_2930_;
}
else
{
v_x_2921_ = v_tail_2927_;
v_x_2922_ = v_tail_2929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3___boxed(lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
uint8_t v_res_2934_; lean_object* v_r_2935_; 
v_res_2934_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_x_2932_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec(v_x_2932_);
v_r_2935_ = lean_box(v_res_2934_);
return v_r_2935_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(lean_object* v_x_2936_, lean_object* v_x_2937_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
if (lean_obj_tag(v_x_2937_) == 0)
{
uint8_t v___x_2938_; 
v___x_2938_ = 1;
return v___x_2938_;
}
else
{
uint8_t v___x_2939_; 
v___x_2939_ = 0;
return v___x_2939_;
}
}
else
{
if (lean_obj_tag(v_x_2937_) == 0)
{
uint8_t v___x_2940_; 
v___x_2940_ = 0;
return v___x_2940_;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v_head_2943_; lean_object* v_tail_2944_; uint8_t v___y_2946_; lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v_fst_2950_; lean_object* v_snd_2951_; uint8_t v___x_2952_; 
v_head_2941_ = lean_ctor_get(v_x_2936_, 0);
v_tail_2942_ = lean_ctor_get(v_x_2936_, 1);
v_head_2943_ = lean_ctor_get(v_x_2937_, 0);
v_tail_2944_ = lean_ctor_get(v_x_2937_, 1);
v_fst_2948_ = lean_ctor_get(v_head_2941_, 0);
v_snd_2949_ = lean_ctor_get(v_head_2941_, 1);
v_fst_2950_ = lean_ctor_get(v_head_2943_, 0);
v_snd_2951_ = lean_ctor_get(v_head_2943_, 1);
v___x_2952_ = lean_name_eq(v_fst_2948_, v_fst_2950_);
if (v___x_2952_ == 0)
{
v___y_2946_ = v___x_2952_;
goto v___jp_2945_;
}
else
{
uint8_t v___x_2953_; 
v___x_2953_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_snd_2949_, v_snd_2951_);
v___y_2946_ = v___x_2953_;
goto v___jp_2945_;
}
v___jp_2945_:
{
if (v___y_2946_ == 0)
{
return v___y_2946_;
}
else
{
v_x_2936_ = v_tail_2942_;
v_x_2937_ = v_tail_2944_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1___boxed(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
uint8_t v_res_2956_; lean_object* v_r_2957_; 
v_res_2956_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_x_2954_, v_x_2955_);
lean_dec(v_x_2955_);
lean_dec(v_x_2954_);
v_r_2957_ = lean_box(v_res_2956_);
return v_r_2957_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_2961_, lean_object* v_newName_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_ref_2968_; 
v_ref_2968_ = lean_ctor_get(v_a_2965_, 5);
if (lean_obj_tag(v_ref_2968_) == 3)
{
lean_object* v_val_2969_; uint8_t v___x_2970_; 
v_val_2969_ = lean_ctor_get(v_ref_2968_, 2);
v___x_2970_ = l_Lean_Name_hasMacroScopes(v_val_2969_);
if (v___x_2970_ == 0)
{
uint8_t v___x_2971_; lean_object* v___x_3049_; 
v___x_2971_ = 1;
v___x_3049_ = l_Lean_Syntax_getRange_x3f(v_ref_2968_, v___x_2971_);
if (lean_obj_tag(v___x_3049_) == 0)
{
if (v___x_2970_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec(v_newName_2962_);
lean_dec(v_declName_2961_);
v___x_3050_ = lean_box(0);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
else
{
goto v___jp_2972_;
}
}
else
{
lean_dec_ref_known(v___x_3049_, 1);
goto v___jp_2972_;
}
v___jp_2972_:
{
lean_object* v___x_2973_; 
lean_inc(v_val_2969_);
v___x_2973_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_val_2969_, v___x_2971_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3040_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_3040_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3040_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_declName_2961_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v___x_2978_);
v___x_2981_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_a_2974_, v___x_2980_);
lean_dec_ref_known(v___x_2980_, 2);
lean_dec(v_a_2974_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
lean_dec(v_newName_2962_);
v___x_2982_ = lean_box(0);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2982_);
v___x_2984_ = v___x_2976_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
else
{
lean_object* v___x_2986_; 
lean_del_object(v___x_2976_);
v___x_2986_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_newName_2962_, v___x_2970_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3031_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3031_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3031_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
if (lean_obj_tag(v_a_2987_) == 1)
{
lean_object* v_val_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2989_);
v_val_2991_ = lean_ctor_get(v_a_2987_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2993_ = v_a_2987_;
v_isShared_2994_ = v_isSharedCheck_3026_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_val_2991_);
lean_dec(v_a_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3026_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_2995_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_2996_ = l_Lean_Name_toString(v_val_2991_, v___x_2971_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_ctor_set(v___x_2999_, 3, v___x_2998_);
lean_ctor_set(v___x_2999_, 4, v___x_2998_);
lean_ctor_set(v___x_2999_, 5, v___x_2998_);
v___x_3000_ = 0;
v___x_3001_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_2998_);
lean_ctor_set(v___x_3001_, 2, v___x_2998_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*3, v___x_3000_);
v___x_3002_ = lean_unsigned_to_nat(1u);
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_3002_);
v___x_3004_ = lean_array_push(v___x_3003_, v___x_3001_);
lean_inc_ref(v_ref_2968_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v_ref_2968_);
v___x_3006_ = v___x_2993_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_ref_2968_);
v___x_3006_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_MessageData_hint(v___x_2995_, v___x_3004_, v___x_3006_, v___x_2998_, v___x_2970_, v_a_2965_, v_a_2966_);
lean_dec_ref(v___x_3004_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3016_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_a_3008_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3007_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3007_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_dec(v_a_2987_);
v___x_3027_ = lean_box(0);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_3027_);
v___x_3029_ = v___x_2989_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2986_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2986_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_newName_2962_);
lean_dec(v_declName_2961_);
v_a_3041_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2973_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2973_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec(v_newName_2962_);
lean_dec(v_declName_2961_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec(v_newName_2962_);
lean_dec(v_declName_2961_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_3056_, lean_object* v_newName_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3056_, v_newName_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(lean_object* v_opt_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_3064_, v___y_3067_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_opt_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(v_opt_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_opt_3071_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(lean_object* v_00_u03b4_3078_, lean_object* v_t_3079_, lean_object* v_k_3080_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_3079_, v_k_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b4_3082_, lean_object* v_t_3083_, lean_object* v_k_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(v_00_u03b4_3082_, v_t_3083_, v_k_3084_);
lean_dec(v_k_3084_);
lean_dec(v_t_3083_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(lean_object* v_givenName_3086_, uint8_t v_skipAuxDecl_3087_, lean_object* v_auxDeclToFullName_3088_, lean_object* v___x_3089_, lean_object* v_givenNameView_3090_, lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_3086_, v_skipAuxDecl_3087_, v_auxDeclToFullName_3088_, v___x_3089_, v_givenNameView_3090_, v_as_3091_, v_i_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_givenName_3095_, lean_object* v_skipAuxDecl_3096_, lean_object* v_auxDeclToFullName_3097_, lean_object* v___x_3098_, lean_object* v_givenNameView_3099_, lean_object* v_as_3100_, lean_object* v_i_3101_, lean_object* v_a_3102_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3103_; lean_object* v_res_3104_; 
v_skipAuxDecl_boxed_3103_ = lean_unbox(v_skipAuxDecl_3096_);
v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(v_givenName_3095_, v_skipAuxDecl_boxed_3103_, v_auxDeclToFullName_3097_, v___x_3098_, v_givenNameView_3099_, v_as_3100_, v_i_3101_, v_a_3102_);
lean_dec_ref(v_as_3100_);
lean_dec(v_auxDeclToFullName_3097_);
lean_dec(v_givenName_3095_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(lean_object* v_localDecl_x3f_3105_, lean_object* v_givenName_3106_, lean_object* v_as_3107_, lean_object* v_i_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_3105_, v_givenName_3106_, v_as_3107_, v_i_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___boxed(lean_object* v_localDecl_x3f_3111_, lean_object* v_givenName_3112_, lean_object* v_as_3113_, lean_object* v_i_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(v_localDecl_x3f_3111_, v_givenName_3112_, v_as_3113_, v_i_3114_, v_a_3115_);
lean_dec_ref(v_as_3113_);
lean_dec(v_givenName_3112_);
lean_dec(v_localDecl_x3f_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(lean_object* v_n_u2080_3117_, lean_object* v_filter_3118_, lean_object* v_view_x3f_3119_, lean_object* v_as_3120_, lean_object* v_as_x27_3121_, lean_object* v_b_3122_, lean_object* v_a_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_3117_, v_filter_3118_, v_view_x3f_3119_, v_as_x27_3121_, v_b_3122_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_n_u2080_3130_, lean_object* v_filter_3131_, lean_object* v_view_x3f_3132_, lean_object* v_as_3133_, lean_object* v_as_x27_3134_, lean_object* v_b_3135_, lean_object* v_a_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(v_n_u2080_3130_, v_filter_3131_, v_view_x3f_3132_, v_as_3133_, v_as_x27_3134_, v_b_3135_, v_a_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_as_x27_3134_);
lean_dec(v_as_3133_);
lean_dec(v_n_u2080_3130_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(lean_object* v_givenName_3143_, uint8_t v_skipAuxDecl_3144_, lean_object* v_auxDeclToFullName_3145_, lean_object* v___x_3146_, lean_object* v_givenNameView_3147_, lean_object* v_as_3148_, lean_object* v_i_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_3143_, v_skipAuxDecl_3144_, v_auxDeclToFullName_3145_, v___x_3146_, v_givenNameView_3147_, v_as_3148_, v_i_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___boxed(lean_object* v_givenName_3152_, lean_object* v_skipAuxDecl_3153_, lean_object* v_auxDeclToFullName_3154_, lean_object* v___x_3155_, lean_object* v_givenNameView_3156_, lean_object* v_as_3157_, lean_object* v_i_3158_, lean_object* v_a_3159_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3160_; lean_object* v_res_3161_; 
v_skipAuxDecl_boxed_3160_ = lean_unbox(v_skipAuxDecl_3153_);
v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(v_givenName_3152_, v_skipAuxDecl_boxed_3160_, v_auxDeclToFullName_3154_, v___x_3155_, v_givenNameView_3156_, v_as_3157_, v_i_3158_, v_a_3159_);
lean_dec_ref(v_as_3157_);
lean_dec(v_auxDeclToFullName_3154_);
lean_dec(v_givenName_3152_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(lean_object* v_localDecl_x3f_3162_, lean_object* v_givenName_3163_, lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_3162_, v_givenName_3163_, v_as_3164_, v_i_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___boxed(lean_object* v_localDecl_x3f_3168_, lean_object* v_givenName_3169_, lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(v_localDecl_x3f_3168_, v_givenName_3169_, v_as_3170_, v_i_3171_, v_a_3172_);
lean_dec_ref(v_as_3170_);
lean_dec(v_givenName_3169_);
lean_dec(v_localDecl_x3f_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(lean_object* v_opt_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_3174_, v___y_3177_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___boxed(lean_object* v_opt_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(v_opt_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v_opt_3181_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; lean_object* v_env_3192_; lean_object* v___x_3193_; lean_object* v_toEnvExtension_3194_; lean_object* v_asyncMode_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_merged_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v___x_3191_ = lean_st_ref_get(v___y_3189_);
v_env_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc_ref(v_env_3192_);
lean_dec(v___x_3191_);
v___x_3193_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3194_ = lean_ctor_get(v___x_3193_, 0);
v_asyncMode_3195_ = lean_ctor_get(v_toEnvExtension_3194_, 2);
v___x_3196_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3197_ = lean_box(0);
v___x_3198_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3196_, v___x_3193_, v_env_3192_, v_asyncMode_3195_, v___x_3197_);
v_merged_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v___x_3198_, 1);
lean_dec(v_unused_3208_);
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_merged_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_merged_3199_);
lean_ctor_set(v___x_3201_, 0, v_o_3188_);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_o_3188_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_merged_3199_);
v___x_3204_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3209_, v___y_3210_);
lean_dec(v___y_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_options_3218_; lean_object* v___x_3219_; 
v_options_3218_ = lean_ctor_get(v___y_3215_, 2);
lean_inc_ref(v_options_3218_);
v___x_3219_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_3218_, v___y_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3225_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3256_ = l_Lean_MessageData_ofFormat(v___x_3255_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3259_ = l_Lean_stringToMessageData(v___x_3258_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3262_ = l_Lean_stringToMessageData(v___x_3261_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3265_ = l_Lean_stringToMessageData(v___x_3264_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3268_ = l_Lean_stringToMessageData(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__29(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__28));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__31(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__30));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3275_, uint8_t v_allowSuggestion_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3455_; 
v___x_3282_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3455_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3455_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; uint8_t v___x_3288_; lean_object* v_extraMsg_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; 
v___x_3287_ = l_Lean_Linter_linter_deprecated;
v___x_3288_ = l_Lean_Linter_getLinterValue(v___x_3287_, v_a_3283_);
lean_dec(v_a_3283_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3306_; 
lean_dec(v_declName_3275_);
v___x_3304_ = lean_box(0);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3304_);
v___x_3306_ = v___x_3285_;
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
else
{
lean_object* v___x_3308_; lean_object* v_env_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3308_ = lean_st_ref_get(v_a_3280_);
v_env_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc_ref(v_env_3309_);
lean_dec(v___x_3308_);
v___x_3310_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3311_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3275_);
v___x_3312_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3310_, v___x_3311_, v_env_3309_, v_declName_3275_);
if (lean_obj_tag(v___x_3312_) == 1)
{
lean_object* v_val_3313_; lean_object* v_text_x3f_3314_; 
lean_del_object(v___x_3285_);
v_val_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_val_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v_text_x3f_3314_ = lean_ctor_get(v_val_3313_, 1);
if (lean_obj_tag(v_text_x3f_3314_) == 0)
{
lean_object* v_newName_x3f_3315_; 
v_newName_x3f_3315_ = lean_ctor_get(v_val_3313_, 0);
lean_inc(v_newName_x3f_3315_);
lean_dec(v_val_3313_);
if (lean_obj_tag(v_newName_x3f_3315_) == 0)
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_3290_ = v___x_3316_;
v___y_3291_ = v_a_3277_;
v___y_3292_ = v_a_3278_;
v___y_3293_ = v_a_3279_;
v___y_3294_ = v_a_3280_;
goto v___jp_3289_;
}
else
{
lean_object* v_val_3317_; lean_object* v___x_3318_; lean_object* v_env_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; 
v_val_3317_ = lean_ctor_get(v_newName_x3f_3315_, 0);
lean_inc_n(v_val_3317_, 2);
lean_dec_ref_known(v_newName_x3f_3315_, 1);
v___x_3318_ = lean_st_ref_get(v_a_3280_);
v_env_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc_ref_n(v_env_3319_, 2);
lean_dec(v___x_3318_);
v___x_3320_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3321_ = l_Lean_MessageData_ofConstName(v_val_3317_, v___x_3288_);
lean_inc_ref(v___x_3321_);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = l_Lean_Name_getPrefix(v_declName_3275_);
v___x_3326_ = 0;
lean_inc(v_declName_3275_);
v___x_3327_ = l_Lean_Environment_find_x3f(v_env_3319_, v_declName_3275_, v___x_3326_);
if (lean_obj_tag(v___x_3327_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_val_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Lean_Name_getPrefix(v_val_3317_);
lean_inc(v_val_3317_);
lean_inc_ref(v_env_3319_);
v___x_3330_ = l_Lean_Environment_find_x3f(v_env_3319_, v_val_3317_, v___x_3326_);
if (lean_obj_tag(v___x_3330_) == 1)
{
lean_object* v_val_3331_; lean_object* v___x_3332_; 
v_val_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3328_, v_val_3331_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v_msg_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3387_; lean_object* v___y_3388_; uint8_t v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint8_t v___y_3393_; lean_object* v_msg_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; uint8_t v___x_3427_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3427_ = lean_unbox(v_a_3333_);
if (v___x_3427_ == 0)
{
if (v___x_3288_ == 0)
{
lean_dec(v_val_3331_);
lean_dec(v_val_3328_);
v_msg_3420_ = v___x_3324_;
v___y_3421_ = v_a_3277_;
v___y_3422_ = v_a_3278_;
v___y_3423_ = v_a_3279_;
v___y_3424_ = v_a_3280_;
goto v___jp_3419_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3428_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_3429_ = l_Lean_ConstantInfo_type(v_val_3331_);
lean_dec(v_val_3331_);
v___x_3430_ = l_Lean_indentExpr(v___x_3429_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3428_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_ConstantInfo_type(v_val_3328_);
lean_dec(v_val_3328_);
v___x_3435_ = l_Lean_indentExpr(v___x_3434_);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3433_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_MessageData_note(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3324_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v_msg_3420_ = v___x_3438_;
v___y_3421_ = v_a_3277_;
v___y_3422_ = v_a_3278_;
v___y_3423_ = v_a_3279_;
v___y_3424_ = v_a_3280_;
goto v___jp_3419_;
}
}
else
{
lean_dec(v_val_3331_);
lean_dec(v_val_3328_);
v_msg_3420_ = v___x_3324_;
v___y_3421_ = v_a_3277_;
v___y_3422_ = v_a_3278_;
v___y_3423_ = v_a_3279_;
v___y_3424_ = v_a_3280_;
goto v___jp_3419_;
}
v___jp_3334_:
{
if (v_allowSuggestion_3276_ == 0)
{
lean_dec(v_a_3333_);
lean_dec(v_val_3317_);
v_extraMsg_3290_ = v_msg_3335_;
v___y_3291_ = v___y_3336_;
v___y_3292_ = v___y_3337_;
v___y_3293_ = v___y_3338_;
v___y_3294_ = v___y_3339_;
goto v___jp_3289_;
}
else
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_unbox(v_a_3333_);
lean_dec(v_a_3333_);
if (v___x_3340_ == 0)
{
lean_dec(v_val_3317_);
v_extraMsg_3290_ = v_msg_3335_;
v___y_3291_ = v___y_3336_;
v___y_3292_ = v___y_3337_;
v___y_3293_ = v___y_3338_;
v___y_3294_ = v___y_3339_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3341_; 
lean_inc(v_declName_3275_);
v___x_3341_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3275_, v_val_3317_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
if (lean_obj_tag(v_a_3342_) == 1)
{
lean_object* v_val_3343_; lean_object* v___x_3344_; 
v_val_3343_ = lean_ctor_get(v_a_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v_a_3342_, 1);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_msg_3335_);
lean_ctor_set(v___x_3344_, 1, v_val_3343_);
v_extraMsg_3290_ = v___x_3344_;
v___y_3291_ = v___y_3336_;
v___y_3292_ = v___y_3337_;
v___y_3293_ = v___y_3338_;
v___y_3294_ = v___y_3339_;
goto v___jp_3289_;
}
else
{
lean_dec(v_a_3342_);
v_extraMsg_3290_ = v_msg_3335_;
v___y_3291_ = v___y_3336_;
v___y_3292_ = v___y_3337_;
v___y_3293_ = v___y_3338_;
v___y_3294_ = v___y_3339_;
goto v___jp_3289_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v_msg_3335_);
lean_dec(v_declName_3275_);
v_a_3345_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3341_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3341_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
}
v___jp_3353_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3360_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___x_3321_);
v___x_3362_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___y_3359_);
v___x_3365_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_MessageData_ofName(v___x_3329_);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3368_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = l_Lean_MessageData_note(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___y_3355_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v_msg_3335_ = v___x_3372_;
v___y_3336_ = v___y_3358_;
v___y_3337_ = v___y_3357_;
v___y_3338_ = v___y_3356_;
v___y_3339_ = v___y_3354_;
goto v___jp_3334_;
}
v___jp_3373_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3380_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___y_3379_);
v___x_3382_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_MessageData_note(v___x_3383_);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___y_3375_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v_msg_3335_ = v___x_3385_;
v___y_3336_ = v___y_3378_;
v___y_3337_ = v___y_3377_;
v___y_3338_ = v___y_3376_;
v___y_3339_ = v___y_3374_;
goto v___jp_3334_;
}
v___jp_3386_:
{
if (v___y_3393_ == 0)
{
uint8_t v___x_3394_; 
lean_inc(v_declName_3275_);
lean_inc_ref(v_env_3319_);
v___x_3394_ = l_Lean_isProtected(v_env_3319_, v_declName_3275_);
if (v___x_3394_ == 0)
{
if (v___x_3288_ == 0)
{
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
v_msg_3335_ = v___y_3388_;
v___y_3336_ = v___y_3392_;
v___y_3337_ = v___y_3391_;
v___y_3338_ = v___y_3390_;
v___y_3339_ = v___y_3387_;
goto v___jp_3334_;
}
else
{
uint8_t v___x_3395_; 
lean_inc(v_val_3317_);
v___x_3395_ = l_Lean_isProtected(v_env_3319_, v_val_3317_);
if (v___x_3395_ == 0)
{
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3321_);
v_msg_3335_ = v___y_3388_;
v___y_3336_ = v___y_3392_;
v___y_3337_ = v___y_3391_;
v___y_3338_ = v___y_3390_;
v___y_3339_ = v___y_3387_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
lean_inc(v___x_3329_);
v___x_3396_ = l_Lean_Name_componentsRev(v___x_3329_);
v___x_3397_ = lean_unsigned_to_nat(1u);
v___x_3398_ = l_List_lengthTR___redArg(v___x_3396_);
v___x_3399_ = lean_nat_dec_lt(v___x_3397_, v___x_3398_);
lean_dec(v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec(v___x_3396_);
v___x_3400_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___y_3354_ = v___y_3387_;
v___y_3355_ = v___y_3388_;
v___y_3356_ = v___y_3390_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3392_;
v___y_3359_ = v___x_3400_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3401_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___x_3402_ = lean_unsigned_to_nat(0u);
v___x_3403_ = l_List_get___redArg(v___x_3396_, v___x_3402_);
lean_dec(v___x_3396_);
v___x_3404_ = l_Lean_MessageData_ofName(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3401_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___y_3354_ = v___y_3387_;
v___y_3355_ = v___y_3388_;
v___y_3356_ = v___y_3390_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3392_;
v___y_3359_ = v___x_3407_;
goto v___jp_3353_;
}
}
}
}
else
{
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
v_msg_3335_ = v___y_3388_;
v___y_3336_ = v___y_3392_;
v___y_3337_ = v___y_3391_;
v___y_3338_ = v___y_3390_;
v___y_3339_ = v___y_3387_;
goto v___jp_3334_;
}
}
else
{
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
if (lean_obj_tag(v_declName_3275_) == 1)
{
lean_object* v_str_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_str_3408_ = lean_ctor_get(v_declName_3275_, 1);
v___x_3409_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
lean_inc_ref(v_str_3408_);
v___x_3410_ = l_Lean_stringToMessageData(v_str_3408_);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
lean_inc(v_val_3317_);
v___x_3414_ = l_Lean_MessageData_ofConstName(v_val_3317_, v___y_3389_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__29, &l_Lean_Linter_checkDeprecated___closed__29_once, _init_l_Lean_Linter_checkDeprecated___closed__29);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___y_3374_ = v___y_3387_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___y_3392_;
v___y_3379_ = v___x_3417_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_MessageData_nil;
v___y_3374_ = v___y_3387_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___y_3392_;
v___y_3379_ = v___x_3418_;
goto v___jp_3373_;
}
}
}
v___jp_3419_:
{
uint8_t v___x_3425_; 
v___x_3425_ = l_Lean_Name_isAnonymous(v___x_3325_);
if (v___x_3425_ == 0)
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_name_eq(v___x_3325_, v___x_3329_);
lean_dec(v___x_3325_);
if (v___x_3426_ == 0)
{
v___y_3387_ = v___y_3424_;
v___y_3388_ = v_msg_3420_;
v___y_3389_ = v___x_3425_;
v___y_3390_ = v___y_3423_;
v___y_3391_ = v___y_3422_;
v___y_3392_ = v___y_3421_;
v___y_3393_ = v___x_3288_;
goto v___jp_3386_;
}
else
{
v___y_3387_ = v___y_3424_;
v___y_3388_ = v_msg_3420_;
v___y_3389_ = v___x_3425_;
v___y_3390_ = v___y_3423_;
v___y_3391_ = v___y_3422_;
v___y_3392_ = v___y_3421_;
v___y_3393_ = v___x_3425_;
goto v___jp_3386_;
}
}
else
{
lean_dec(v___x_3329_);
lean_dec(v___x_3325_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
v_msg_3335_ = v_msg_3420_;
v___y_3336_ = v___y_3421_;
v___y_3337_ = v___y_3422_;
v___y_3338_ = v___y_3423_;
v___y_3339_ = v___y_3424_;
goto v___jp_3334_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_val_3331_);
lean_dec(v___x_3329_);
lean_dec(v_val_3328_);
lean_dec(v___x_3325_);
lean_dec_ref_known(v___x_3324_, 2);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
lean_dec(v_val_3317_);
lean_dec(v_declName_3275_);
v_a_3439_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3332_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3332_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
lean_dec(v_val_3328_);
lean_dec(v___x_3325_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
lean_dec(v_val_3317_);
v_extraMsg_3290_ = v___x_3324_;
v___y_3291_ = v_a_3277_;
v___y_3292_ = v_a_3278_;
v___y_3293_ = v_a_3279_;
v___y_3294_ = v_a_3280_;
goto v___jp_3289_;
}
}
else
{
lean_dec(v___x_3327_);
lean_dec(v___x_3325_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_env_3319_);
lean_dec(v_val_3317_);
v_extraMsg_3290_ = v___x_3324_;
v___y_3291_ = v_a_3277_;
v___y_3292_ = v_a_3278_;
v___y_3293_ = v_a_3279_;
v___y_3294_ = v_a_3280_;
goto v___jp_3289_;
}
}
}
else
{
lean_object* v_val_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_inc_ref(v_text_x3f_3314_);
lean_dec(v_val_3313_);
v_val_3447_ = lean_ctor_get(v_text_x3f_3314_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v_text_x3f_3314_, 1);
v___x_3448_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__31, &l_Lean_Linter_checkDeprecated___closed__31_once, _init_l_Lean_Linter_checkDeprecated___closed__31);
v___x_3449_ = l_Lean_stringToMessageData(v_val_3447_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v_extraMsg_3290_ = v___x_3450_;
v___y_3291_ = v_a_3277_;
v___y_3292_ = v_a_3278_;
v___y_3293_ = v_a_3279_;
v___y_3294_ = v_a_3280_;
goto v___jp_3289_;
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
lean_dec(v___x_3312_);
lean_dec(v_declName_3275_);
v___x_3451_ = lean_box(0);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3451_);
v___x_3453_ = v___x_3285_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
v___jp_3289_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_3296_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3297_ = l_Lean_MessageData_ofConstName(v_declName_3275_, v___x_3288_);
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v_extraMsg_3290_);
v___x_3302_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3295_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_3302_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3456_, lean_object* v_allowSuggestion_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
uint8_t v_allowSuggestion_boxed_3463_; lean_object* v_res_3464_; 
v_allowSuggestion_boxed_3463_ = lean_unbox(v_allowSuggestion_3457_);
v_res_3464_ = l_Lean_Linter_checkDeprecated(v_declName_3456_, v_allowSuggestion_boxed_3463_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3465_, v___y_3469_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
return v_res_3478_;
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
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_();
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
