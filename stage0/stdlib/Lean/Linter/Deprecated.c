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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_15890__boxed_190_; uint8_t v_suppressElabErrors_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v___y_15890__boxed_190_ = lean_unbox(v___y_187_);
v_suppressElabErrors_boxed_191_ = lean_unbox(v_suppressElabErrors_188_);
v_res_192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_15890__boxed_190_, v_suppressElabErrors_boxed_191_, v_x_189_);
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
uint8_t v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; uint8_t v___y_295_; lean_object* v___y_296_; lean_object* v___y_314_; uint8_t v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_325_; uint8_t v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; uint8_t v___y_330_; uint8_t v___y_331_; uint8_t v___x_336_; uint8_t v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; uint8_t v___y_344_; uint8_t v___y_346_; uint8_t v___x_361_; 
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
lean_ctor_set(v___x_278_, 1, v___y_259_);
lean_inc_ref(v___y_257_);
lean_inc_ref(v___y_255_);
v___x_279_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_279_, 0, v___y_255_);
lean_ctor_set(v___x_279_, 1, v___y_254_);
lean_ctor_set(v___x_279_, 2, v___y_256_);
lean_ctor_set(v___x_279_, 3, v___y_257_);
lean_ctor_set(v___x_279_, 4, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5, v___y_258_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5 + 1, v___y_253_);
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
lean_inc_ref_n(v___y_293_, 2);
v___x_303_ = l_Lean_FileMap_toPosition(v___y_293_, v___y_291_);
lean_dec(v___y_291_);
v___x_304_ = l_Lean_FileMap_toPosition(v___y_293_, v___y_296_);
lean_dec(v___y_296_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_292_ == 0)
{
lean_del_object(v___x_301_);
lean_dec_ref(v___y_289_);
v___y_253_ = v___y_290_;
v___y_254_ = v___x_303_;
v___y_255_ = v___y_294_;
v___y_256_ = v___x_305_;
v___y_257_ = v___x_306_;
v___y_258_ = v___y_295_;
v___y_259_ = v_a_299_;
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
v___y_253_ = v___y_290_;
v___y_254_ = v___x_303_;
v___y_255_ = v___y_294_;
v___y_256_ = v___x_305_;
v___y_257_ = v___x_306_;
v___y_258_ = v___y_295_;
v___y_259_ = v_a_299_;
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
v___x_322_ = l_Lean_Syntax_getTailPos_x3f(v___y_318_, v___y_320_);
lean_dec(v___y_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_inc(v___y_321_);
v___y_289_ = v___y_314_;
v___y_290_ = v___y_315_;
v___y_291_ = v___y_321_;
v___y_292_ = v___y_316_;
v___y_293_ = v___y_317_;
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
v___y_292_ = v___y_316_;
v___y_293_ = v___y_317_;
v___y_294_ = v___y_319_;
v___y_295_ = v___y_320_;
v___y_296_ = v_val_323_;
goto v___jp_288_;
}
}
v___jp_324_:
{
lean_object* v_ref_332_; lean_object* v___x_333_; 
v_ref_332_ = l_Lean_replaceRef(v_ref_245_, v___y_329_);
v___x_333_ = l_Lean_Syntax_getPos_x3f(v_ref_332_, v___y_330_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___y_314_ = v___y_325_;
v___y_315_ = v___y_331_;
v___y_316_ = v___y_326_;
v___y_317_ = v___y_327_;
v___y_318_ = v_ref_332_;
v___y_319_ = v___y_328_;
v___y_320_ = v___y_330_;
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
v___y_316_ = v___y_326_;
v___y_317_ = v___y_327_;
v___y_318_ = v_ref_332_;
v___y_319_ = v___y_328_;
v___y_320_ = v___y_330_;
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
v___y_328_ = v___y_340_;
v___y_329_ = v___y_341_;
v___y_330_ = v___y_343_;
v___y_331_ = v_severity_247_;
goto v___jp_324_;
}
else
{
v___y_325_ = v___y_342_;
v___y_326_ = v___y_338_;
v___y_327_ = v___y_339_;
v___y_328_ = v___y_340_;
v___y_329_ = v___y_341_;
v___y_330_ = v___y_343_;
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
v___y_338_ = v_suppressElabErrors_351_;
v___y_339_ = v_fileMap_348_;
v___y_340_ = v_fileName_347_;
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
v___y_338_ = v_suppressElabErrors_351_;
v___y_339_ = v_fileMap_348_;
v___y_340_ = v_fileName_347_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
lean_object* v_key_459_; lean_object* v_value_460_; lean_object* v_tail_461_; uint8_t v___x_462_; 
v_key_459_ = lean_ctor_get(v_x_457_, 0);
v_value_460_ = lean_ctor_get(v_x_457_, 1);
v_tail_461_ = lean_ctor_get(v_x_457_, 2);
v___x_462_ = lean_name_eq(v_key_459_, v_a_456_);
if (v___x_462_ == 0)
{
v_x_457_ = v_tail_461_;
goto _start;
}
else
{
lean_object* v___x_464_; 
lean_inc(v_value_460_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v_value_460_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_a_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_465_, v_x_466_);
lean_dec(v_x_466_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_buckets_470_; lean_object* v___x_471_; uint64_t v___y_473_; 
v_buckets_470_ = lean_ctor_get(v_m_468_, 1);
v___x_471_ = lean_array_get_size(v_buckets_470_);
if (lean_obj_tag(v_a_469_) == 0)
{
uint64_t v___x_487_; 
v___x_487_ = 1723ULL;
v___y_473_ = v___x_487_;
goto v___jp_472_;
}
else
{
uint64_t v_hash_488_; 
v_hash_488_ = lean_ctor_get_uint64(v_a_469_, sizeof(void*)*2);
v___y_473_ = v_hash_488_;
goto v___jp_472_;
}
v___jp_472_:
{
uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v_fold_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_474_ = 32ULL;
v___x_475_ = lean_uint64_shift_right(v___y_473_, v___x_474_);
v_fold_476_ = lean_uint64_xor(v___y_473_, v___x_475_);
v___x_477_ = 16ULL;
v___x_478_ = lean_uint64_shift_right(v_fold_476_, v___x_477_);
v___x_479_ = lean_uint64_xor(v_fold_476_, v___x_478_);
v___x_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = lean_usize_of_nat(v___x_471_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_sub(v___x_481_, v___x_482_);
v___x_484_ = lean_usize_land(v___x_480_, v___x_483_);
v___x_485_ = lean_array_uget_borrowed(v_buckets_470_, v___x_484_);
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_469_, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_m_489_);
return v_res_491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(lean_object* v_keys_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_get_size(v_keys_492_);
v___x_496_ = lean_nat_dec_lt(v_i_493_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v_i_493_);
return v___x_496_;
}
else
{
lean_object* v_k_x27_497_; uint8_t v___x_498_; 
v_k_x27_497_ = lean_array_fget_borrowed(v_keys_492_, v_i_493_);
v___x_498_ = l_Lean_instBEqExtraModUse_beq(v_k_494_, v_k_x27_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_i_493_, v___x_499_);
lean_dec(v_i_493_);
v_i_493_ = v___x_500_;
goto _start;
}
else
{
lean_dec(v_i_493_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_keys_502_, lean_object* v_i_503_, lean_object* v_k_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_502_, v_i_503_, v_k_504_);
lean_dec_ref(v_k_504_);
lean_dec_ref(v_keys_502_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_x_507_, size_t v_x_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_es_510_; lean_object* v___x_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v_j_514_; lean_object* v___x_515_; 
v_es_510_ = lean_ctor_get(v_x_507_, 0);
v___x_511_ = lean_box(2);
v___x_512_ = ((size_t)31ULL);
v___x_513_ = lean_usize_land(v_x_508_, v___x_512_);
v_j_514_ = lean_usize_to_nat(v___x_513_);
v___x_515_ = lean_array_get_borrowed(v___x_511_, v_es_510_, v_j_514_);
lean_dec(v_j_514_);
switch(lean_obj_tag(v___x_515_))
{
case 0:
{
lean_object* v_key_516_; uint8_t v___x_517_; 
v_key_516_ = lean_ctor_get(v___x_515_, 0);
v___x_517_ = l_Lean_instBEqExtraModUse_beq(v_x_509_, v_key_516_);
return v___x_517_;
}
case 1:
{
lean_object* v_node_518_; size_t v___x_519_; size_t v___x_520_; 
v_node_518_ = lean_ctor_get(v___x_515_, 0);
v___x_519_ = ((size_t)5ULL);
v___x_520_ = lean_usize_shift_right(v_x_508_, v___x_519_);
v_x_507_ = v_node_518_;
v_x_508_ = v___x_520_;
goto _start;
}
default: 
{
uint8_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
}
}
else
{
lean_object* v_ks_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_ks_523_ = lean_ctor_get(v_x_507_, 0);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_ks_523_, v___x_524_, v_x_509_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
size_t v_x_16437__boxed_529_; uint8_t v_res_530_; lean_object* v_r_531_; 
v_x_16437__boxed_529_ = lean_unbox_usize(v_x_527_);
lean_dec(v_x_527_);
v_res_530_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_526_, v_x_16437__boxed_529_, v_x_528_);
lean_dec_ref(v_x_528_);
lean_dec_ref(v_x_526_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
uint64_t v___x_534_; size_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_instHashableExtraModUse_hash(v_x_533_);
v___x_535_ = lean_uint64_to_usize(v___x_534_);
v___x_536_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_532_, v___x_535_, v_x_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_537_, v_x_538_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v_x_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_541_; double v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_float_of_nat(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_cls_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_ref_550_; lean_object* v___x_551_; lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_596_; 
v_ref_550_ = lean_ctor_get(v___y_547_, 5);
v___x_551_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0(v_msg_546_, v___y_547_, v___y_548_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_596_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v_traceState_557_; lean_object* v_env_558_; lean_object* v_nextMacroScope_559_; lean_object* v_ngen_560_; lean_object* v_auxDeclNGen_561_; lean_object* v_cache_562_; lean_object* v_messages_563_; lean_object* v_infoState_564_; lean_object* v_snapshotTasks_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_595_; 
v___x_556_ = lean_st_ref_take(v___y_548_);
v_traceState_557_ = lean_ctor_get(v___x_556_, 4);
v_env_558_ = lean_ctor_get(v___x_556_, 0);
v_nextMacroScope_559_ = lean_ctor_get(v___x_556_, 1);
v_ngen_560_ = lean_ctor_get(v___x_556_, 2);
v_auxDeclNGen_561_ = lean_ctor_get(v___x_556_, 3);
v_cache_562_ = lean_ctor_get(v___x_556_, 5);
v_messages_563_ = lean_ctor_get(v___x_556_, 6);
v_infoState_564_ = lean_ctor_get(v___x_556_, 7);
v_snapshotTasks_565_ = lean_ctor_get(v___x_556_, 8);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_595_ == 0)
{
v___x_567_ = v___x_556_;
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snapshotTasks_565_);
lean_inc(v_infoState_564_);
lean_inc(v_messages_563_);
lean_inc(v_cache_562_);
lean_inc(v_traceState_557_);
lean_inc(v_auxDeclNGen_561_);
lean_inc(v_ngen_560_);
lean_inc(v_nextMacroScope_559_);
lean_inc(v_env_558_);
lean_dec(v___x_556_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint64_t v_tid_569_; lean_object* v_traces_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_594_; 
v_tid_569_ = lean_ctor_get_uint64(v_traceState_557_, sizeof(void*)*1);
v_traces_570_ = lean_ctor_get(v_traceState_557_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_traceState_557_);
if (v_isSharedCheck_594_ == 0)
{
v___x_572_ = v_traceState_557_;
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_traces_570_);
lean_dec(v_traceState_557_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; double v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0);
v___x_576_ = 0;
v___x_577_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_578_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_578_, 0, v_cls_545_);
lean_ctor_set(v___x_578_, 1, v___x_574_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_ctor_set_float(v___x_578_, sizeof(void*)*3, v___x_575_);
lean_ctor_set_float(v___x_578_, sizeof(void*)*3 + 8, v___x_575_);
lean_ctor_set_uint8(v___x_578_, sizeof(void*)*3 + 16, v___x_576_);
v___x_579_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1));
v___x_580_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v_a_552_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_inc(v_ref_550_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_ref_550_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_PersistentArray_push___redArg(v_traces_570_, v___x_581_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_582_);
v___x_584_ = v___x_572_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_582_);
lean_ctor_set_uint64(v_reuseFailAlloc_593_, sizeof(void*)*1, v_tid_569_);
v___x_584_ = v_reuseFailAlloc_593_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v___x_584_);
v___x_586_ = v___x_567_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_env_558_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_nextMacroScope_559_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_ngen_560_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_auxDeclNGen_561_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_592_, 5, v_cache_562_);
lean_ctor_set(v_reuseFailAlloc_592_, 6, v_messages_563_);
lean_ctor_set(v_reuseFailAlloc_592_, 7, v_infoState_564_);
lean_ctor_set(v_reuseFailAlloc_592_, 8, v_snapshotTasks_565_);
v___x_586_ = v_reuseFailAlloc_592_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = lean_st_ref_put(v___y_548_, v___x_586_);
v___x_588_ = lean_box(0);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_588_);
v___x_590_ = v___x_554_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_cls_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_597_, v_msg_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_607_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_608_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_cls_626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_627_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_628_ = l_Lean_Name_append(v___x_627_, v_cls_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_639_, uint8_t v_isMeta_640_, lean_object* v_hint_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; uint8_t v_isExporting_647_; lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_entry_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v_isExporting_647_ = lean_ctor_get_uint8(v_env_646_, sizeof(void*)*8);
lean_dec_ref(v_env_646_);
v___x_648_ = lean_st_ref_get(v___y_643_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_639_);
v_entry_651_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_651_, 0, v_mod_639_);
lean_ctor_set_uint8(v_entry_651_, sizeof(void*)*1, v_isExporting_647_);
lean_ctor_set_uint8(v_entry_651_, sizeof(void*)*1 + 1, v_isMeta_640_);
v___x_652_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_653_ = lean_box(1);
v___x_654_ = lean_box(0);
v___x_681_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_650_, v___x_652_, v_env_649_, v___x_653_, v___x_654_);
v___x_682_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v___x_681_, v_entry_651_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v_options_683_; uint8_t v_hasTrace_684_; 
v_options_683_ = lean_ctor_get(v___y_642_, 2);
v_hasTrace_684_ = lean_ctor_get_uint8(v_options_683_, sizeof(void*)*1);
if (v_hasTrace_684_ == 0)
{
lean_dec(v_hint_641_);
lean_dec(v_mod_639_);
v___y_656_ = v___y_643_;
goto v___jp_655_;
}
else
{
lean_object* v_inheritedTraceOptions_685_; lean_object* v_cls_686_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_inheritedTraceOptions_685_ = lean_ctor_get(v___y_642_, 13);
v_cls_686_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_706_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__14);
v___x_707_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_685_, v_options_683_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v_hint_641_);
lean_dec(v_mod_639_);
v___y_656_ = v___y_643_;
goto v___jp_655_;
}
else
{
lean_object* v___x_708_; lean_object* v___y_710_; 
v___x_708_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__16);
if (v_isExporting_647_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_710_ = v___x_717_;
goto v___jp_709_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__22));
v___y_710_ = v___x_718_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc_ref(v___y_710_);
v___x_711_ = l_Lean_stringToMessageData(v___y_710_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_708_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__18);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
if (v_isMeta_640_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_693_ = v___x_714_;
v___y_694_ = v___x_715_;
goto v___jp_692_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__20));
v___y_693_ = v___x_714_;
v___y_694_ = v___x_716_;
goto v___jp_692_;
}
}
}
v___jp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___y_688_);
lean_ctor_set(v___x_690_, 1, v___y_689_);
v___x_691_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_686_, v___x_690_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_dec_ref_known(v___x_691_, 1);
v___y_656_ = v___y_643_;
goto v___jp_655_;
}
else
{
lean_dec_ref_known(v_entry_651_, 1);
return v___x_691_;
}
}
v___jp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
lean_inc_ref(v___y_694_);
v___x_695_ = l_Lean_stringToMessageData(v___y_694_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___y_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__9);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_Lean_MessageData_ofName(v_mod_639_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_Name_isAnonymous(v_hint_641_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__11);
v___x_703_ = l_Lean_MessageData_ofName(v_hint_641_);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___y_688_ = v___x_700_;
v___y_689_ = v___x_704_;
goto v___jp_687_;
}
else
{
lean_object* v___x_705_; 
lean_dec(v_hint_641_);
v___x_705_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v___y_688_ = v___x_700_;
v___y_689_ = v___x_705_;
goto v___jp_687_;
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref_known(v_entry_651_, 1);
lean_dec(v_hint_641_);
lean_dec(v_mod_639_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v_toEnvExtension_658_; lean_object* v_env_659_; lean_object* v_nextMacroScope_660_; lean_object* v_ngen_661_; lean_object* v_auxDeclNGen_662_; lean_object* v_traceState_663_; lean_object* v_messages_664_; lean_object* v_infoState_665_; lean_object* v_snapshotTasks_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_679_; 
v___x_657_ = lean_st_ref_take(v___y_656_);
v_toEnvExtension_658_ = lean_ctor_get(v___x_652_, 0);
v_env_659_ = lean_ctor_get(v___x_657_, 0);
v_nextMacroScope_660_ = lean_ctor_get(v___x_657_, 1);
v_ngen_661_ = lean_ctor_get(v___x_657_, 2);
v_auxDeclNGen_662_ = lean_ctor_get(v___x_657_, 3);
v_traceState_663_ = lean_ctor_get(v___x_657_, 4);
v_messages_664_ = lean_ctor_get(v___x_657_, 6);
v_infoState_665_ = lean_ctor_get(v___x_657_, 7);
v_snapshotTasks_666_ = lean_ctor_get(v___x_657_, 8);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_657_, 5);
lean_dec(v_unused_680_);
v___x_668_ = v___x_657_;
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snapshotTasks_666_);
lean_inc(v_infoState_665_);
lean_inc(v_messages_664_);
lean_inc(v_traceState_663_);
lean_inc(v_auxDeclNGen_662_);
lean_inc(v_ngen_661_);
lean_inc(v_nextMacroScope_660_);
lean_inc(v_env_659_);
lean_dec(v___x_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_asyncMode_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_asyncMode_670_ = lean_ctor_get(v_toEnvExtension_658_, 2);
v___x_671_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_652_, v_env_659_, v_entry_651_, v_asyncMode_670_, v___x_654_);
v___x_672_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__5);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 5, v___x_672_);
lean_ctor_set(v___x_668_, 0, v___x_671_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_nextMacroScope_660_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_ngen_661_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_auxDeclNGen_662_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_traceState_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_messages_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_infoState_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_snapshotTasks_666_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_st_ref_put(v___y_656_, v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_721_, lean_object* v_isMeta_722_, lean_object* v_hint_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_isMeta_boxed_727_; lean_object* v_res_728_; 
v_isMeta_boxed_727_ = lean_unbox(v_isMeta_722_);
v_res_728_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_mod_721_, v_isMeta_boxed_727_, v_hint_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_729_, lean_object* v_declName_730_, lean_object* v_as_731_, size_t v_sz_732_, size_t v_i_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_733_, v_sz_732_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec(v_declName_730_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_b_734_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; lean_object* v_modules_741_; lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v_toImport_745_; lean_object* v_module_746_; uint8_t v___x_747_; lean_object* v___x_748_; 
v___x_740_ = l_Lean_Environment_header(v___x_729_);
v_modules_741_ = lean_ctor_get(v___x_740_, 3);
lean_inc_ref(v_modules_741_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_743_ = lean_array_uget_borrowed(v_as_731_, v_i_733_);
v___x_744_ = lean_array_get(v___x_742_, v_modules_741_, v_a_743_);
lean_dec_ref(v_modules_741_);
v_toImport_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_toImport_745_);
lean_dec(v___x_744_);
v_module_746_ = lean_ctor_get(v_toImport_745_, 0);
lean_inc(v_module_746_);
lean_dec_ref(v_toImport_745_);
v___x_747_ = 0;
lean_inc(v_declName_730_);
v___x_748_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_module_746_, v___x_747_, v_declName_730_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v___x_749_; size_t v___x_750_; size_t v___x_751_; 
lean_dec_ref_known(v___x_748_, 1);
v___x_749_ = lean_box(0);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_733_, v___x_750_);
v_i_733_ = v___x_751_;
v_b_734_ = v___x_749_;
goto _start;
}
else
{
lean_dec(v_declName_730_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_753_, lean_object* v_declName_754_, lean_object* v_as_755_, lean_object* v_sz_756_, lean_object* v_i_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_756_);
lean_dec(v_sz_756_);
v_i_boxed_763_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(v___x_753_, v_declName_754_, v_as_755_, v_sz_boxed_762_, v_i_boxed_763_, v_b_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec_ref(v_as_755_);
lean_dec_ref(v___x_753_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__1));
v___x_768_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__0));
v___x_769_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_768_, v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(lean_object* v_declName_772_, uint8_t v_isMeta_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v_env_781_; lean_object* v___y_783_; lean_object* v___x_796_; 
v___x_777_ = lean_st_ref_get(v___y_775_);
v_env_781_ = lean_ctor_get(v___x_777_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_777_);
v___x_796_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_781_, v_declName_772_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_dec_ref(v_env_781_);
lean_dec(v_declName_772_);
goto v___jp_778_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v_modules_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_val_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_Environment_header(v_env_781_);
v_modules_799_ = lean_ctor_get(v___x_798_, 3);
lean_inc_ref(v_modules_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = lean_array_get_size(v_modules_799_);
v___x_801_ = lean_nat_dec_lt(v_val_797_, v___x_800_);
if (v___x_801_ == 0)
{
lean_dec_ref(v_modules_799_);
lean_dec(v_val_797_);
lean_dec_ref(v_env_781_);
lean_dec(v_declName_772_);
goto v___jp_778_;
}
else
{
lean_object* v___x_802_; lean_object* v_env_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___y_807_; 
v___x_802_ = lean_st_ref_get(v___y_775_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__2);
v___x_805_ = lean_array_fget(v_modules_799_, v_val_797_);
lean_dec(v_val_797_);
lean_dec_ref(v_modules_799_);
if (v_isMeta_773_ == 0)
{
lean_dec_ref(v_env_803_);
v___y_807_ = v_isMeta_773_;
goto v___jp_806_;
}
else
{
uint8_t v___x_818_; 
lean_inc(v_declName_772_);
v___x_818_ = l_Lean_isMarkedMeta(v_env_803_, v_declName_772_);
if (v___x_818_ == 0)
{
v___y_807_ = v_isMeta_773_;
goto v___jp_806_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 0;
v___y_807_ = v___x_819_;
goto v___jp_806_;
}
}
v___jp_806_:
{
lean_object* v_toImport_808_; lean_object* v_module_809_; lean_object* v___x_810_; 
v_toImport_808_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_toImport_808_);
lean_dec(v___x_805_);
v_module_809_ = lean_ctor_get(v_toImport_808_, 0);
lean_inc(v_module_809_);
lean_dec_ref(v_toImport_808_);
lean_inc(v_declName_772_);
v___x_810_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4(v_module_809_, v___y_807_, v_declName_772_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = l_Lean_indirectModUseExt;
v___x_812_ = lean_box(1);
v___x_813_ = lean_box(0);
lean_inc_ref(v_env_781_);
v___x_814_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_804_, v___x_811_, v_env_781_, v___x_812_, v___x_813_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_814_, v_declName_772_);
lean_dec(v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___closed__3));
v___y_783_ = v___x_816_;
goto v___jp_782_;
}
else
{
lean_object* v_val_817_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_815_, 1);
v___y_783_ = v_val_817_;
goto v___jp_782_;
}
}
else
{
lean_dec_ref(v_env_781_);
lean_dec(v_declName_772_);
return v___x_810_;
}
}
}
}
v___jp_778_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
v___jp_782_:
{
lean_object* v___x_784_; size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_box(0);
v_sz_785_ = lean_array_size(v___y_783_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__5(v_env_781_, v_declName_772_, v___y_783_, v_sz_785_, v___x_786_, v___x_784_, v___y_774_, v___y_775_);
lean_dec_ref(v___y_783_);
lean_dec_ref(v_env_781_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_787_, 0);
lean_dec(v_unused_795_);
v___x_789_ = v___x_787_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_dec(v___x_787_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_784_);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_784_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_820_, lean_object* v_isMeta_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
uint8_t v_isMeta_boxed_825_; lean_object* v_res_826_; 
v_isMeta_boxed_825_ = lean_unbox(v_isMeta_821_);
v_res_826_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(v_declName_820_, v_isMeta_boxed_825_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_826_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_831_ = l_Lean_MessageData_ofFormat(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_836_ = l_Lean_MessageData_ofFormat(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_850_ = l_Lean_MessageData_ofFormat(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_852_ = l_Lean_MessageData_hint_x27(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_860_ = l_Lean_MessageData_ofFormat(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_868_ = l_Lean_MessageData_ofFormat(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_875_ = l_Lean_MessageData_ofFormat(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_box(1);
v___x_880_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_881_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
lean_ctor_set(v___x_887_, 3, v___x_886_);
lean_ctor_set(v___x_887_, 4, v___x_885_);
lean_ctor_set(v___x_887_, 5, v___x_885_);
lean_ctor_set(v___x_887_, 6, v___x_885_);
lean_ctor_set(v___x_887_, 7, v___x_885_);
lean_ctor_set(v___x_887_, 8, v___x_885_);
lean_ctor_set(v___x_887_, 9, v___x_885_);
lean_ctor_set(v___x_887_, 10, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_889_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
lean_ctor_set(v___x_889_, 4, v___x_888_);
lean_ctor_set(v___x_889_, 5, v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
lean_ctor_set(v___x_891_, 4, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_893_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_894_ = lean_box(1);
v___x_895_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_896_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
lean_ctor_set(v___x_897_, 3, v___x_893_);
lean_ctor_set(v___x_897_, 4, v___x_892_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v_declName_907_, lean_object* v_stx_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v_hint_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; 
v___x_918_ = l_Lean_Name_mkStr2(v___x_904_, v___x_905_);
lean_inc(v_stx_908_);
v___x_919_ = l_Lean_Syntax_isOfKind(v_stx_908_, v___x_918_);
lean_dec(v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1028_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1029_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1028_, v___y_909_, v___y_910_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v_val_1042_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v_a_1091_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v_a_1168_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v_since_x3f_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v_typeChanged_x3f_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1224_; lean_object* v_text_x3f_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v_id_x3f_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1250_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1031_);
v___x_1251_ = l_Lean_Syntax_isNone(v___x_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
lean_inc(v___x_1250_);
v___x_1252_ = l_Lean_Syntax_matchesNull(v___x_1250_, v___x_1031_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v___x_1250_);
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1253_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1254_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1253_, v___y_909_, v___y_910_);
return v___x_1254_;
}
else
{
lean_object* v_id_x3f_1255_; lean_object* v___x_1256_; 
v_id_x3f_1255_ = l_Lean_Syntax_getArg(v___x_1250_, v___x_1030_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_id_x3f_1255_);
v_id_x3f_1238_ = v___x_1256_;
v___y_1239_ = v___y_909_;
v___y_1240_ = v___y_910_;
goto v___jp_1237_;
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v___x_1250_);
v___x_1257_ = lean_box(0);
v_id_x3f_1238_ = v___x_1257_;
v___y_1239_ = v___y_909_;
v___y_1240_ = v___y_910_;
goto v___jp_1237_;
}
v___jp_1032_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1043_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___f_906_);
v___x_1048_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1044_);
lean_ctor_set(v___x_1048_, 1, v___x_1045_);
lean_ctor_set(v___x_1048_, 2, v___x_1045_);
lean_ctor_set(v___x_1048_, 3, v___x_1045_);
lean_ctor_set(v___x_1048_, 4, v___x_1046_);
lean_ctor_set(v___x_1048_, 5, v___x_1047_);
lean_inc(v_val_1042_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_val_1042_);
lean_ctor_set(v___x_1049_, 1, v_val_1042_);
v___x_1050_ = l_Lean_Syntax_ofRange(v___x_1049_, v___x_919_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = 4;
v___x_1053_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1048_);
lean_ctor_set(v___x_1053_, 1, v___x_1051_);
lean_ctor_set(v___x_1053_, 2, v___x_1045_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*3, v___x_1052_);
v___x_1054_ = lean_mk_empty_array_with_capacity(v___x_1031_);
v___x_1055_ = lean_array_push(v___x_1054_, v___x_1053_);
v___x_1056_ = l_Lean_MessageData_hint(v___x_1043_, v___x_1055_, v___x_1045_, v___x_1045_, v___y_1037_, v___y_1036_, v___y_1038_);
lean_dec_ref(v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_988_ = v___y_1034_;
v___y_989_ = v___y_1033_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1040_;
v___y_992_ = v___y_1039_;
v___y_993_ = v___y_1041_;
v_hint_994_ = v_a_1057_;
v___y_995_ = v___y_1036_;
v___y_996_ = v___y_1038_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
v_a_1058_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
v___jp_1066_:
{
if (lean_obj_tag(v___y_1068_) == 0)
{
lean_dec_ref(v___f_906_);
v___y_1019_ = v___y_1067_;
v___y_1020_ = v___y_1068_;
v___y_1021_ = v___y_1071_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1072_;
v___y_1024_ = v___y_1074_;
v___y_1025_ = v___y_1073_;
v___y_1026_ = v___y_1075_;
goto v___jp_1018_;
}
else
{
lean_object* v_val_1076_; lean_object* v___x_1077_; 
v_val_1076_ = lean_ctor_get(v___y_1068_, 0);
v___x_1077_ = l_Lean_Syntax_getTailPos_x3f(v_val_1076_, v___x_919_);
if (lean_obj_tag(v___x_1077_) == 1)
{
lean_object* v_val_1078_; 
v_val_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___y_1033_ = v___y_1067_;
v___y_1034_ = v___y_1068_;
v___y_1035_ = v___y_1071_;
v___y_1036_ = v___y_1070_;
v___y_1037_ = v___y_1069_;
v___y_1038_ = v___y_1072_;
v___y_1039_ = v___y_1074_;
v___y_1040_ = v___y_1073_;
v___y_1041_ = v___y_1075_;
v_val_1042_ = v_val_1078_;
goto v___jp_1032_;
}
else
{
lean_dec(v___x_1077_);
lean_dec_ref(v___f_906_);
v___y_1019_ = v___y_1067_;
v___y_1020_ = v___y_1068_;
v___y_1021_ = v___y_1071_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1072_;
v___y_1024_ = v___y_1074_;
v___y_1025_ = v___y_1073_;
v___y_1026_ = v___y_1075_;
goto v___jp_1018_;
}
}
}
v___jp_1079_:
{
if (v_a_1091_ == 0)
{
if (lean_obj_tag(v___y_1081_) == 0)
{
if (v___y_1080_ == 0)
{
lean_dec_ref(v___y_1089_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1082_;
v___y_972_ = v___y_1086_;
v___y_973_ = v___y_1088_;
v___y_974_ = v___y_1090_;
v___y_975_ = v___y_1085_;
v___y_976_ = v___y_1087_;
goto v___jp_970_;
}
else
{
if (lean_obj_tag(v___y_1090_) == 0)
{
v___y_1067_ = v___y_1083_;
v___y_1068_ = v___y_1082_;
v___y_1069_ = v___y_1084_;
v___y_1070_ = v___y_1085_;
v___y_1071_ = v___y_1086_;
v___y_1072_ = v___y_1087_;
v___y_1073_ = v___y_1088_;
v___y_1074_ = v___y_1089_;
v___y_1075_ = v___y_1090_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1093_; 
v_val_1092_ = lean_ctor_get(v___y_1090_, 0);
v___x_1093_ = l_Lean_Syntax_getTailPos_x3f(v_val_1092_, v___x_919_);
if (lean_obj_tag(v___x_1093_) == 0)
{
v___y_1067_ = v___y_1083_;
v___y_1068_ = v___y_1082_;
v___y_1069_ = v___y_1084_;
v___y_1070_ = v___y_1085_;
v___y_1071_ = v___y_1086_;
v___y_1072_ = v___y_1087_;
v___y_1073_ = v___y_1088_;
v___y_1074_ = v___y_1089_;
v___y_1075_ = v___y_1090_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1094_; 
v_val_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___y_1033_ = v___y_1083_;
v___y_1034_ = v___y_1082_;
v___y_1035_ = v___y_1086_;
v___y_1036_ = v___y_1085_;
v___y_1037_ = v___y_1084_;
v___y_1038_ = v___y_1087_;
v___y_1039_ = v___y_1089_;
v___y_1040_ = v___y_1088_;
v___y_1041_ = v___y_1090_;
v_val_1042_ = v_val_1094_;
goto v___jp_1032_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_1081_, 1);
lean_dec_ref(v___y_1089_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1082_;
v___y_972_ = v___y_1086_;
v___y_973_ = v___y_1088_;
v___y_974_ = v___y_1090_;
v___y_975_ = v___y_1085_;
v___y_976_ = v___y_1087_;
goto v___jp_970_;
}
}
else
{
lean_dec_ref(v___y_1089_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___f_906_);
if (lean_obj_tag(v___y_1081_) == 0)
{
v___y_971_ = v___y_1082_;
v___y_972_ = v___y_1086_;
v___y_973_ = v___y_1088_;
v___y_974_ = v___y_1090_;
v___y_975_ = v___y_1085_;
v___y_976_ = v___y_1087_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref_known(v___y_1081_, 1);
v___x_1095_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1096_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_1095_, v___y_1085_, v___y_1087_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref_known(v___x_1096_, 1);
v___y_971_ = v___y_1082_;
v___y_972_ = v___y_1086_;
v___y_973_ = v___y_1088_;
v___y_974_ = v___y_1090_;
v___y_975_ = v___y_1085_;
v___y_976_ = v___y_1087_;
goto v___jp_970_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v___y_1090_);
lean_dec(v___y_1088_);
lean_dec(v___y_1086_);
lean_dec(v___y_1082_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
v___jp_1105_:
{
if (lean_obj_tag(v___y_1109_) == 1)
{
lean_object* v_val_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
v_val_1113_ = lean_ctor_get(v___y_1109_, 0);
v___x_1114_ = 0;
lean_inc(v_val_1113_);
v___x_1115_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2(v_val_1113_, v___x_1114_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
lean_dec_ref_known(v___x_1115_, 1);
v___x_1116_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3(v___y_1111_, v___y_1112_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = l_Lean_Linter_linter_deprecated;
v___x_1119_ = l_Lean_Linter_getLinterValue(v___x_1118_, v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1119_ == 0)
{
lean_dec(v___y_1106_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1107_;
v___y_972_ = v___y_1108_;
v___y_973_ = v___y_1109_;
v___y_974_ = v___y_1110_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1120_; lean_object* v_env_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_st_ref_get(v___y_1112_);
v_env_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref_n(v_env_1121_, 2);
lean_dec(v___x_1120_);
v___x_1122_ = l_Lean_Environment_find_x3f(v_env_1121_, v_declName_907_, v___x_1114_);
if (lean_obj_tag(v___x_1122_) == 1)
{
lean_object* v_val_1123_; lean_object* v___x_1124_; 
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v___x_1122_, 1);
lean_inc(v_val_1113_);
v___x_1124_ = l_Lean_Environment_find_x3f(v_env_1121_, v_val_1113_, v___x_1114_);
if (lean_obj_tag(v___x_1124_) == 1)
{
lean_object* v_val_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; uint64_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_val_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = 1;
v___x_1127_ = 0;
v___x_1128_ = 2;
v___x_1129_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1129_, 0, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 1, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 2, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 3, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 4, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 5, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 6, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 7, v___x_1114_);
lean_ctor_set_uint8(v___x_1129_, 8, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 9, v___x_1126_);
lean_ctor_set_uint8(v___x_1129_, 10, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, 11, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 12, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 13, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 14, v___x_1128_);
lean_ctor_set_uint8(v___x_1129_, 15, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 16, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 17, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 18, v___x_1119_);
lean_ctor_set_uint8(v___x_1129_, 19, v___x_1114_);
v___x_1130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set_uint64(v___x_1131_, sizeof(void*)*1, v___x_1130_);
v___x_1132_ = lean_box(1);
v___x_1133_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1134_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1136_, 0, v___x_1131_);
lean_ctor_set(v___x_1136_, 1, v___x_1132_);
lean_ctor_set(v___x_1136_, 2, v___x_1133_);
lean_ctor_set(v___x_1136_, 3, v___x_1134_);
lean_ctor_set(v___x_1136_, 4, v___x_1135_);
lean_ctor_set(v___x_1136_, 5, v___x_1030_);
lean_ctor_set(v___x_1136_, 6, v___x_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7, v___x_1114_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 1, v___x_1114_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 2, v___x_1114_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*7 + 3, v___x_919_);
v___x_1137_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1138_ = lean_st_mk_ref(v___x_1137_);
v___x_1139_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_1123_, v_val_1125_, v___x_1136_, v___x_1138_, v___y_1111_, v___y_1112_);
lean_dec_ref_known(v___x_1136_, 7);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_st_ref_get(v___x_1138_);
lean_dec(v___x_1138_);
lean_dec(v___x_1141_);
v___x_1142_ = lean_unbox(v_a_1140_);
lean_dec(v_a_1140_);
v___y_1080_ = v___x_1119_;
v___y_1081_ = v___y_1106_;
v___y_1082_ = v___y_1107_;
v___y_1083_ = v_val_1123_;
v___y_1084_ = v___x_1114_;
v___y_1085_ = v___y_1111_;
v___y_1086_ = v___y_1108_;
v___y_1087_ = v___y_1112_;
v___y_1088_ = v___y_1109_;
v___y_1089_ = v_val_1125_;
v___y_1090_ = v___y_1110_;
v_a_1091_ = v___x_1142_;
goto v___jp_1079_;
}
else
{
lean_dec(v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1143_; uint8_t v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1144_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
v___y_1080_ = v___x_1119_;
v___y_1081_ = v___y_1106_;
v___y_1082_ = v___y_1107_;
v___y_1083_ = v_val_1123_;
v___y_1084_ = v___x_1114_;
v___y_1085_ = v___y_1111_;
v___y_1086_ = v___y_1108_;
v___y_1087_ = v___y_1112_;
v___y_1088_ = v___y_1109_;
v___y_1089_ = v_val_1125_;
v___y_1090_ = v___y_1110_;
v_a_1091_ = v___x_1144_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_val_1125_);
lean_dec(v_val_1123_);
lean_dec_ref_known(v___y_1109_, 1);
lean_dec(v___y_1110_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___f_906_);
v_a_1145_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1139_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1139_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_dec(v___x_1124_);
lean_dec(v_val_1123_);
lean_dec(v___y_1106_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1107_;
v___y_972_ = v___y_1108_;
v___y_973_ = v___y_1109_;
v___y_974_ = v___y_1110_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
}
else
{
lean_dec(v___x_1122_);
lean_dec_ref(v_env_1121_);
lean_dec(v___y_1106_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1107_;
v___y_972_ = v___y_1108_;
v___y_973_ = v___y_1109_;
v___y_974_ = v___y_1110_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref_known(v___y_1109_, 1);
lean_dec(v___y_1110_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v_a_1153_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1115_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1115_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_dec(v___y_1106_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1107_;
v___y_972_ = v___y_1108_;
v___y_973_ = v___y_1109_;
v___y_974_ = v___y_1110_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
}
v___jp_1161_:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
lean_inc(v_declName_907_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_declName_907_);
v___x_1170_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__4(v_a_1168_, v___x_1169_);
lean_dec_ref_known(v___x_1169_, 1);
if (v___x_1170_ == 0)
{
v___y_1106_ = v___y_1164_;
v___y_1107_ = v___y_1165_;
v___y_1108_ = v___y_1166_;
v___y_1109_ = v_a_1168_;
v___y_1110_ = v___y_1167_;
v___y_1111_ = v___y_1162_;
v___y_1112_ = v___y_1163_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___f_906_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1172_ = l_Lean_MessageData_ofConstName(v_declName_907_, v___x_919_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1175_, v___y_1162_, v___y_1163_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
v___jp_1185_:
{
if (lean_obj_tag(v___y_1186_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
v___y_1162_ = v___y_1190_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1186_;
v___y_1166_ = v_since_x3f_1189_;
v___y_1167_ = v___y_1188_;
v_a_1168_ = v___x_1192_;
goto v___jp_1161_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_val_1193_ = lean_ctor_get(v___y_1186_, 0);
v___x_1194_ = lean_box(0);
lean_inc(v_val_1193_);
v___x_1195_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_val_1193_, v___x_1194_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1196_);
v___y_1162_ = v___y_1190_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1186_;
v___y_1166_ = v_since_x3f_1189_;
v___y_1167_ = v___y_1188_;
v_a_1168_ = v___x_1197_;
goto v___jp_1161_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref_known(v___y_1186_, 1);
lean_dec(v_since_x3f_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v_a_1198_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1195_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1195_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_unsigned_to_nat(4u);
v___x_1214_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1213_);
lean_dec(v_stx_908_);
v___x_1215_ = l_Lean_Syntax_isNone(v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1214_);
v___x_1217_ = l_Lean_Syntax_matchesNull(v___x_1214_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v___x_1214_);
lean_dec(v_typeChanged_x3f_1210_);
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1218_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1218_, v___y_1211_, v___y_1212_);
return v___x_1219_;
}
else
{
lean_object* v_since_x3f_1220_; lean_object* v___x_1221_; 
v_since_x3f_1220_ = l_Lean_Syntax_getArg(v___x_1214_, v___y_1209_);
lean_dec(v___x_1214_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_since_x3f_1220_);
v___y_1186_ = v___y_1207_;
v___y_1187_ = v_typeChanged_x3f_1210_;
v___y_1188_ = v___y_1208_;
v_since_x3f_1189_ = v___x_1221_;
v___y_1190_ = v___y_1211_;
v___y_1191_ = v___y_1212_;
goto v___jp_1185_;
}
}
else
{
lean_object* v___x_1222_; 
lean_dec(v___x_1214_);
v___x_1222_ = lean_box(0);
v___y_1186_ = v___y_1207_;
v___y_1187_ = v_typeChanged_x3f_1210_;
v___y_1188_ = v___y_1208_;
v_since_x3f_1189_ = v___x_1222_;
v___y_1190_ = v___y_1211_;
v___y_1191_ = v___y_1212_;
goto v___jp_1185_;
}
}
v___jp_1223_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1228_ = lean_unsigned_to_nat(3u);
v___x_1229_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1228_);
v___x_1230_ = l_Lean_Syntax_isNone(v___x_1229_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
lean_inc(v___x_1229_);
v___x_1231_ = l_Lean_Syntax_matchesNull(v___x_1229_, v___x_1031_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v___x_1229_);
lean_dec(v_text_x3f_1225_);
lean_dec(v___y_1224_);
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1232_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1233_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1232_, v___y_1226_, v___y_1227_);
return v___x_1233_;
}
else
{
lean_object* v_typeChanged_x3f_1234_; lean_object* v___x_1235_; 
v_typeChanged_x3f_1234_ = l_Lean_Syntax_getArg(v___x_1229_, v___x_1030_);
lean_dec(v___x_1229_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_typeChanged_x3f_1234_);
v___y_1207_ = v___y_1224_;
v___y_1208_ = v_text_x3f_1225_;
v___y_1209_ = v___x_1228_;
v_typeChanged_x3f_1210_ = v___x_1235_;
v___y_1211_ = v___y_1226_;
v___y_1212_ = v___y_1227_;
goto v___jp_1206_;
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v___x_1229_);
v___x_1236_ = lean_box(0);
v___y_1207_ = v___y_1224_;
v___y_1208_ = v_text_x3f_1225_;
v___y_1209_ = v___x_1228_;
v_typeChanged_x3f_1210_ = v___x_1236_;
v___y_1211_ = v___y_1226_;
v___y_1212_ = v___y_1227_;
goto v___jp_1206_;
}
}
v___jp_1237_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(2u);
v___x_1242_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_1241_);
v___x_1243_ = l_Lean_Syntax_isNone(v___x_1242_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
lean_inc(v___x_1242_);
v___x_1244_ = l_Lean_Syntax_matchesNull(v___x_1242_, v___x_1031_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v___x_1242_);
lean_dec(v_id_x3f_1238_);
lean_dec(v_stx_908_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1245_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1246_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v___x_1245_, v___y_1239_, v___y_1240_);
return v___x_1246_;
}
else
{
lean_object* v_text_x3f_1247_; lean_object* v___x_1248_; 
v_text_x3f_1247_ = l_Lean_Syntax_getArg(v___x_1242_, v___x_1030_);
lean_dec(v___x_1242_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_text_x3f_1247_);
v___y_1224_ = v_id_x3f_1238_;
v_text_x3f_1225_ = v___x_1248_;
v___y_1226_ = v___y_1239_;
v___y_1227_ = v___y_1240_;
goto v___jp_1223_;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v___x_1242_);
v___x_1249_ = lean_box(0);
v___y_1224_ = v_id_x3f_1238_;
v_text_x3f_1225_ = v___x_1249_;
v___y_1226_ = v___y_1239_;
v___y_1227_ = v___y_1240_;
goto v___jp_1223_;
}
}
}
v___jp_912_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_916_, 0, v___y_915_);
lean_ctor_set(v___x_916_, 1, v___y_913_);
lean_ctor_set(v___x_916_, 2, v___y_914_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
v___jp_920_:
{
if (lean_obj_tag(v___y_922_) == 0)
{
if (v___x_919_ == 0)
{
v___y_913_ = v___y_921_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_923_;
goto v___jp_912_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_927_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_926_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_dec_ref_known(v___x_927_, 1);
v___y_913_ = v___y_921_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_923_;
goto v___jp_912_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v___y_923_);
lean_dec(v___y_921_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
v___y_913_ = v___y_921_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_923_;
goto v___jp_912_;
}
}
v___jp_936_:
{
if (lean_obj_tag(v___y_939_) == 0)
{
if (v___x_919_ == 0)
{
v___y_921_ = v___y_937_;
v___y_922_ = v___y_942_;
v___y_923_ = v___y_941_;
v___y_924_ = v___y_938_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
else
{
if (lean_obj_tag(v___y_937_) == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_944_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_943_, v___y_938_, v___y_940_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref_known(v___x_944_, 1);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_942_;
v___y_923_ = v___y_941_;
v___y_924_ = v___y_938_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v___y_942_);
lean_dec(v___y_941_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
v___y_921_ = v___y_937_;
v___y_922_ = v___y_942_;
v___y_923_ = v___y_941_;
v___y_924_ = v___y_938_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
}
}
else
{
lean_dec_ref_known(v___y_939_, 1);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_942_;
v___y_923_ = v___y_941_;
v___y_924_ = v___y_938_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
}
v___jp_953_:
{
if (lean_obj_tag(v___y_956_) == 0)
{
lean_object* v___x_960_; 
v___x_960_ = lean_box(0);
v___y_937_ = v___y_959_;
v___y_938_ = v___y_954_;
v___y_939_ = v___y_955_;
v___y_940_ = v___y_957_;
v___y_941_ = v___y_958_;
v___y_942_ = v___x_960_;
goto v___jp_936_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_val_961_ = lean_ctor_get(v___y_956_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___y_956_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___y_956_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___y_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_TSyntax_getString(v_val_961_);
lean_dec(v_val_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v___y_937_ = v___y_959_;
v___y_938_ = v___y_954_;
v___y_939_ = v___y_955_;
v___y_940_ = v___y_957_;
v___y_941_ = v___y_958_;
v___y_942_ = v___x_967_;
goto v___jp_936_;
}
}
}
}
v___jp_970_:
{
if (lean_obj_tag(v___y_974_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_box(0);
v___y_954_ = v___y_975_;
v___y_955_ = v___y_971_;
v___y_956_ = v___y_972_;
v___y_957_ = v___y_976_;
v___y_958_ = v___y_973_;
v___y_959_ = v___x_977_;
goto v___jp_953_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_val_978_ = lean_ctor_get(v___y_974_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___y_974_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___y_974_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_val_978_);
lean_dec(v___y_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_TSyntax_getString(v_val_978_);
lean_dec(v_val_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
v___y_954_ = v___y_975_;
v___y_955_ = v___y_971_;
v___y_956_ = v___y_972_;
v___y_957_ = v___y_976_;
v___y_958_ = v___y_973_;
v___y_959_ = v___x_984_;
goto v___jp_953_;
}
}
}
}
v___jp_987_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_997_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_998_ = l_Lean_ConstantInfo_type(v___y_992_);
lean_dec_ref(v___y_992_);
v___x_999_ = l_Lean_indentExpr(v___x_998_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_ConstantInfo_type(v___y_989_);
lean_dec_ref(v___y_989_);
v___x_1004_ = l_Lean_indentExpr(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_hint_994_);
v___x_1009_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1(v___x_1008_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec_ref_known(v___x_1009_, 1);
v___y_971_ = v___y_988_;
v___y_972_ = v___y_990_;
v___y_973_ = v___y_991_;
v___y_974_ = v___y_993_;
v___y_975_ = v___y_995_;
v___y_976_ = v___y_996_;
goto v___jp_970_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___y_993_);
lean_dec(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_988_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
v___jp_1018_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___y_988_ = v___y_1020_;
v___y_989_ = v___y_1019_;
v___y_990_ = v___y_1021_;
v___y_991_ = v___y_1025_;
v___y_992_ = v___y_1024_;
v___y_993_ = v___y_1026_;
v_hint_994_ = v___x_1027_;
v___y_995_ = v___y_1022_;
v___y_996_ = v___y_1023_;
goto v___jp_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v___f_1260_, lean_object* v_declName_1261_, lean_object* v_stx_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v___x_1258_, v___x_1259_, v___f_1260_, v_declName_1261_, v_stx_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(uint8_t v___x_1267_, lean_object* v_env_1268_, lean_object* v_n_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Lean_Environment_contains(v_env_1268_, v_n_1269_, v___x_1267_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v___x_1272_, lean_object* v_env_1273_, lean_object* v_n_1274_, lean_object* v_x_1275_){
_start:
{
uint8_t v___x_17958__boxed_1276_; uint8_t v_res_1277_; lean_object* v_r_1278_; 
v___x_17958__boxed_1276_ = lean_unbox(v___x_1272_);
v_res_1277_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(v___x_17958__boxed_1276_, v_env_1273_, v_n_1274_, v_x_1275_);
lean_dec_ref(v_x_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1309_ = l_Lean_registerParametricAttribute___redArg(v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2____boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___redArg(v_msg_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__0(v_00_u03b1_1318_, v_msg_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1324_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__3_spec__8(v_o_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_1334_, lean_object* v_m_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_1335_, v_a_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_1338_, v_m_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_m_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint8_t v_res_1349_; lean_object* v_r_1350_; 
v_res_1349_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_00_u03b2_1346_, v_x_1347_, v_x_1348_);
lean_dec_ref(v_x_1348_);
lean_dec_ref(v_x_1347_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1351_, lean_object* v_a_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_1352_, v_x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_00_u03b2_1355_, lean_object* v_a_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_00_u03b2_1355_, v_a_1356_, v_x_1357_);
lean_dec(v_x_1357_);
lean_dec(v_a_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_1359_, lean_object* v_x_1360_, size_t v_x_1361_, lean_object* v_x_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_1360_, v_x_1361_, v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
size_t v_x_18097__boxed_1368_; uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_x_18097__boxed_1368_ = lean_unbox_usize(v_x_1366_);
lean_dec(v_x_1366_);
v_res_1369_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(v_00_u03b2_1364_, v_x_1365_, v_x_18097__boxed_1368_, v_x_1367_);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_x_1365_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_k_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_1372_, v_i_1375_, v_k_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_k_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(v_00_u03b2_1378_, v_keys_1379_, v_vals_1380_, v_heq_1381_, v_i_1382_, v_k_1383_);
lean_dec_ref(v_k_1383_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg___lam__0(lean_object* v_declName_1386_, lean_object* v_entry_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_env_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = l_Lean_Linter_deprecatedAttr;
v___x_1393_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1392_, v_env_1391_, v_declName_1386_, v_entry_1387_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_inst_1390_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 3);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = l_Lean_MessageData_ofFormat(v___x_1399_);
v___x_1401_ = l_Lean_throwError___redArg(v_inst_1388_, v_inst_1389_, v___x_1400_);
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_inst_1388_);
v_a_1404_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1405_ = l_Lean_setEnv___redArg(v_inst_1390_, v_a_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___redArg(lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_declName_1409_, lean_object* v_entry_1410_){
_start:
{
lean_object* v_toBind_1411_; lean_object* v_getEnv_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; 
v_toBind_1411_ = lean_ctor_get(v_inst_1406_, 1);
lean_inc(v_toBind_1411_);
v_getEnv_1412_ = lean_ctor_get(v_inst_1407_, 0);
lean_inc(v_getEnv_1412_);
v___f_1413_ = lean_alloc_closure((void*)(l_Lean_Linter_setDeprecated___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1413_, 0, v_declName_1409_);
lean_closure_set(v___f_1413_, 1, v_entry_1410_);
lean_closure_set(v___f_1413_, 2, v_inst_1406_);
lean_closure_set(v___f_1413_, 3, v_inst_1408_);
lean_closure_set(v___f_1413_, 4, v_inst_1407_);
v___x_1414_ = lean_apply_4(v_toBind_1411_, lean_box(0), lean_box(0), v_getEnv_1412_, v___f_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated(lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_declName_1419_, lean_object* v_entry_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Linter_setDeprecated___redArg(v_inst_1416_, v_inst_1417_, v_inst_1418_, v_declName_1419_, v_entry_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isDeprecated(lean_object* v_env_1422_, lean_object* v_declName_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1425_ = l_Lean_Linter_deprecatedAttr;
v___x_1426_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1424_, v___x_1425_, v_env_1422_, v_declName_1423_);
if (lean_obj_tag(v___x_1426_) == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = 0;
return v___x_1427_;
}
else
{
uint8_t v___x_1428_; 
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = 1;
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isDeprecated___boxed(lean_object* v_env_1429_, lean_object* v_declName_1430_){
_start:
{
uint8_t v_res_1431_; lean_object* v_r_1432_; 
v_res_1431_ = l_Lean_Linter_isDeprecated(v_env_1429_, v_declName_1430_);
v_r_1432_ = lean_box(v_res_1431_);
return v_r_1432_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning___lam__0(lean_object* v_x_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_1435_ = lean_name_eq(v_x_1433_, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(lean_object* v_x_1436_){
_start:
{
uint8_t v_res_1437_; lean_object* v_r_1438_; 
v_res_1437_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_1436_);
lean_dec(v_x_1436_);
v_r_1438_ = lean_box(v_res_1437_);
return v_r_1438_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isDeprecationWarning(lean_object* v_msg_1440_){
_start:
{
lean_object* v___f_1441_; uint8_t v___x_1442_; 
v___f_1441_ = ((lean_object*)(l_Lean_MessageData_isDeprecationWarning___closed__0));
v___x_1442_ = l_Lean_MessageData_hasTag(v___f_1441_, v_msg_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isDeprecationWarning___boxed(lean_object* v_msg_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Lean_MessageData_isDeprecationWarning(v_msg_1443_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getDeprecatedNewName(lean_object* v_env_1446_, lean_object* v_declName_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1449_ = l_Lean_Linter_deprecatedAttr;
v___x_1450_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1448_, v___x_1449_, v_env_1446_, v_declName_1447_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_box(0);
return v___x_1451_;
}
else
{
lean_object* v_val_1452_; lean_object* v_newName_x3f_1453_; 
v_val_1452_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v___x_1450_, 1);
v_newName_x3f_1453_ = lean_ctor_get(v_val_1452_, 0);
lean_inc(v_newName_x3f_1453_);
lean_dec(v_val_1452_);
return v_newName_x3f_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(lean_object* v___x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1454_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0___boxed(lean_object* v___x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___lam__0(v___x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(lean_object* v_x_1468_){
_start:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_box(0);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_tail_1471_; lean_object* v_fst_1472_; uint8_t v___x_1473_; 
v_head_1470_ = lean_ctor_get(v_x_1468_, 0);
v_tail_1471_ = lean_ctor_get(v_x_1468_, 1);
v_fst_1472_ = lean_ctor_get(v_head_1470_, 0);
v___x_1473_ = l_Lean_isPrivateName(v_fst_1472_);
if (v___x_1473_ == 0)
{
v_x_1468_ = v_tail_1471_;
goto _start;
}
else
{
lean_object* v___x_1475_; 
lean_inc(v_head_1470_);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_head_1470_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0___boxed(lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_x_1476_);
lean_dec(v_x_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(lean_object* v_msgData_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v_env_1485_; lean_object* v___x_1486_; lean_object* v_mctx_1487_; lean_object* v_lctx_1488_; lean_object* v_options_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1484_ = lean_st_ref_get(v___y_1482_);
v_env_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_ref(v_env_1485_);
lean_dec(v___x_1484_);
v___x_1486_ = lean_st_ref_get(v___y_1480_);
v_mctx_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_mctx_1487_);
lean_dec(v___x_1486_);
v_lctx_1488_ = lean_ctor_get(v___y_1479_, 2);
v_options_1489_ = lean_ctor_get(v___y_1481_, 2);
lean_inc_ref(v_options_1489_);
lean_inc_ref(v_lctx_1488_);
v___x_1490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1490_, 0, v_env_1485_);
lean_ctor_set(v___x_1490_, 1, v_mctx_1487_);
lean_ctor_set(v___x_1490_, 2, v_lctx_1488_);
lean_ctor_set(v___x_1490_, 3, v_options_1489_);
v___x_1491_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_msgData_1478_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19___boxed(lean_object* v_msgData_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v_msgData_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(lean_object* v_ref_1502_, lean_object* v_msgData_1503_, uint8_t v_severity_1504_, uint8_t v_isSilent_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_a_1512_; lean_object* v___y_1516_; uint8_t v___y_1517_; lean_object* v___y_1518_; uint8_t v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1551_; lean_object* v___y_1552_; uint8_t v___y_1553_; uint8_t v___y_1554_; lean_object* v___y_1555_; uint8_t v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1575_; uint8_t v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1586_; lean_object* v___y_1587_; uint8_t v___y_1588_; uint8_t v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1592_; uint8_t v___x_1597_; lean_object* v___y_1599_; uint8_t v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; uint8_t v___y_1605_; uint8_t v___y_1607_; uint8_t v___x_1622_; 
v___x_1597_ = 2;
v___x_1622_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1504_, v___x_1597_);
if (v___x_1622_ == 0)
{
v___y_1607_ = v___x_1622_;
goto v___jp_1606_;
}
else
{
uint8_t v___x_1623_; 
lean_inc_ref(v_msgData_1503_);
v___x_1623_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1503_);
v___y_1607_ = v___x_1623_;
goto v___jp_1606_;
}
v___jp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_a_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
v___jp_1515_:
{
lean_object* v___x_1525_; lean_object* v_currNamespace_1526_; lean_object* v_openDecls_1527_; lean_object* v_env_1528_; lean_object* v_nextMacroScope_1529_; lean_object* v_ngen_1530_; lean_object* v_auxDeclNGen_1531_; lean_object* v_traceState_1532_; lean_object* v_cache_1533_; lean_object* v_messages_1534_; lean_object* v_infoState_1535_; lean_object* v_snapshotTasks_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1549_; 
v___x_1525_ = lean_st_ref_take(v___y_1524_);
v_currNamespace_1526_ = lean_ctor_get(v___y_1523_, 6);
v_openDecls_1527_ = lean_ctor_get(v___y_1523_, 7);
v_env_1528_ = lean_ctor_get(v___x_1525_, 0);
v_nextMacroScope_1529_ = lean_ctor_get(v___x_1525_, 1);
v_ngen_1530_ = lean_ctor_get(v___x_1525_, 2);
v_auxDeclNGen_1531_ = lean_ctor_get(v___x_1525_, 3);
v_traceState_1532_ = lean_ctor_get(v___x_1525_, 4);
v_cache_1533_ = lean_ctor_get(v___x_1525_, 5);
v_messages_1534_ = lean_ctor_get(v___x_1525_, 6);
v_infoState_1535_ = lean_ctor_get(v___x_1525_, 7);
v_snapshotTasks_1536_ = lean_ctor_get(v___x_1525_, 8);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1538_ = v___x_1525_;
v_isShared_1539_ = v_isSharedCheck_1549_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_snapshotTasks_1536_);
lean_inc(v_infoState_1535_);
lean_inc(v_messages_1534_);
lean_inc(v_cache_1533_);
lean_inc(v_traceState_1532_);
lean_inc(v_auxDeclNGen_1531_);
lean_inc(v_ngen_1530_);
lean_inc(v_nextMacroScope_1529_);
lean_inc(v_env_1528_);
lean_dec(v___x_1525_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1549_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_inc(v_openDecls_1527_);
lean_inc(v_currNamespace_1526_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_currNamespace_1526_);
lean_ctor_set(v___x_1540_, 1, v_openDecls_1527_);
v___x_1541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc_ref(v___y_1518_);
v___x_1542_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1542_, 0, v___y_1518_);
lean_ctor_set(v___x_1542_, 1, v___y_1520_);
lean_ctor_set(v___x_1542_, 2, v___y_1516_);
lean_ctor_set(v___x_1542_, 3, v___y_1521_);
lean_ctor_set(v___x_1542_, 4, v___x_1541_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5, v___y_1517_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5 + 1, v___y_1519_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5 + 2, v_isSilent_1505_);
v___x_1543_ = l_Lean_MessageLog_add(v___x_1542_, v_messages_1534_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 6, v___x_1543_);
v___x_1545_ = v___x_1538_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_env_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_nextMacroScope_1529_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_ngen_1530_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_auxDeclNGen_1531_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_traceState_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_cache_1533_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_infoState_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v_snapshotTasks_1536_);
v___x_1545_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_st_ref_put(v___y_1524_, v___x_1545_);
v___x_1547_ = lean_box(0);
v_a_1512_ = v___x_1547_;
goto v___jp_1511_;
}
}
}
v___jp_1550_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1573_; 
v___x_1559_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1503_);
v___x_1560_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_1559_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_inc_ref_n(v___y_1557_, 2);
v___x_1565_ = l_Lean_FileMap_toPosition(v___y_1557_, v___y_1555_);
lean_dec(v___y_1555_);
v___x_1566_ = l_Lean_FileMap_toPosition(v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_1556_ == 0)
{
lean_dec_ref(v___y_1551_);
v___y_1516_ = v___x_1568_;
v___y_1517_ = v___y_1553_;
v___y_1518_ = v___y_1552_;
v___y_1519_ = v___y_1554_;
v___y_1520_ = v___x_1565_;
v___y_1521_ = v___x_1569_;
v___y_1522_ = v_a_1561_;
v___y_1523_ = v___y_1508_;
v___y_1524_ = v___y_1509_;
goto v___jp_1515_;
}
else
{
uint8_t v___x_1570_; 
lean_inc(v_a_1561_);
v___x_1570_ = l_Lean_MessageData_hasTag(v___y_1551_, v_a_1561_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v___x_1568_);
lean_dec_ref(v___x_1565_);
lean_dec(v_a_1561_);
v___x_1571_ = lean_box(0);
v_a_1512_ = v___x_1571_;
goto v___jp_1511_;
}
else
{
v___y_1516_ = v___x_1568_;
v___y_1517_ = v___y_1553_;
v___y_1518_ = v___y_1552_;
v___y_1519_ = v___y_1554_;
v___y_1520_ = v___x_1565_;
v___y_1521_ = v___x_1569_;
v___y_1522_ = v_a_1561_;
v___y_1523_ = v___y_1508_;
v___y_1524_ = v___y_1509_;
goto v___jp_1515_;
}
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Syntax_getTailPos_x3f(v___y_1578_, v___y_1576_);
lean_dec(v___y_1578_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_inc(v___y_1582_);
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1577_;
v___y_1553_ = v___y_1576_;
v___y_1554_ = v___y_1579_;
v___y_1555_ = v___y_1582_;
v___y_1556_ = v___y_1580_;
v___y_1557_ = v___y_1581_;
v___y_1558_ = v___y_1582_;
goto v___jp_1550_;
}
else
{
lean_object* v_val_1584_; 
v_val_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1577_;
v___y_1553_ = v___y_1576_;
v___y_1554_ = v___y_1579_;
v___y_1555_ = v___y_1582_;
v___y_1556_ = v___y_1580_;
v___y_1557_ = v___y_1581_;
v___y_1558_ = v_val_1584_;
goto v___jp_1550_;
}
}
v___jp_1585_:
{
lean_object* v_ref_1593_; lean_object* v___x_1594_; 
v_ref_1593_ = l_Lean_replaceRef(v_ref_1502_, v___y_1591_);
v___x_1594_ = l_Lean_Syntax_getPos_x3f(v_ref_1593_, v___y_1588_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___y_1575_ = v___y_1586_;
v___y_1576_ = v___y_1588_;
v___y_1577_ = v___y_1587_;
v___y_1578_ = v_ref_1593_;
v___y_1579_ = v___y_1592_;
v___y_1580_ = v___y_1589_;
v___y_1581_ = v___y_1590_;
v___y_1582_ = v___x_1595_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1594_, 1);
v___y_1575_ = v___y_1586_;
v___y_1576_ = v___y_1588_;
v___y_1577_ = v___y_1587_;
v___y_1578_ = v_ref_1593_;
v___y_1579_ = v___y_1592_;
v___y_1580_ = v___y_1589_;
v___y_1581_ = v___y_1590_;
v___y_1582_ = v_val_1596_;
goto v___jp_1574_;
}
}
v___jp_1598_:
{
if (v___y_1605_ == 0)
{
v___y_1586_ = v___y_1602_;
v___y_1587_ = v___y_1599_;
v___y_1588_ = v___y_1604_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1601_;
v___y_1591_ = v___y_1603_;
v___y_1592_ = v_severity_1504_;
goto v___jp_1585_;
}
else
{
v___y_1586_ = v___y_1602_;
v___y_1587_ = v___y_1599_;
v___y_1588_ = v___y_1604_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1601_;
v___y_1591_ = v___y_1603_;
v___y_1592_ = v___x_1597_;
goto v___jp_1585_;
}
}
v___jp_1606_:
{
if (v___y_1607_ == 0)
{
lean_object* v_fileName_1608_; lean_object* v_fileMap_1609_; lean_object* v_options_1610_; lean_object* v_ref_1611_; uint8_t v_suppressElabErrors_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; uint8_t v___x_1616_; uint8_t v___x_1617_; 
v_fileName_1608_ = lean_ctor_get(v___y_1508_, 0);
v_fileMap_1609_ = lean_ctor_get(v___y_1508_, 1);
v_options_1610_ = lean_ctor_get(v___y_1508_, 2);
v_ref_1611_ = lean_ctor_get(v___y_1508_, 5);
v_suppressElabErrors_1612_ = lean_ctor_get_uint8(v___y_1508_, sizeof(void*)*14 + 1);
v___x_1613_ = lean_box(v___y_1607_);
v___x_1614_ = lean_box(v_suppressElabErrors_1612_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1615_, 0, v___x_1613_);
lean_closure_set(v___f_1615_, 1, v___x_1614_);
v___x_1616_ = 1;
v___x_1617_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1504_, v___x_1616_);
if (v___x_1617_ == 0)
{
v___y_1599_ = v_fileName_1608_;
v___y_1600_ = v_suppressElabErrors_1612_;
v___y_1601_ = v_fileMap_1609_;
v___y_1602_ = v___f_1615_;
v___y_1603_ = v_ref_1611_;
v___y_1604_ = v___y_1607_;
v___y_1605_ = v___x_1617_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = l_Lean_warningAsError;
v___x_1619_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_1610_, v___x_1618_);
v___y_1599_ = v_fileName_1608_;
v___y_1600_ = v_suppressElabErrors_1612_;
v___y_1601_ = v_fileMap_1609_;
v___y_1602_ = v___f_1615_;
v___y_1603_ = v_ref_1611_;
v___y_1604_ = v___y_1607_;
v___y_1605_ = v___x_1619_;
goto v___jp_1598_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec_ref(v_msgData_1503_);
v___x_1620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___boxed(lean_object* v_ref_1624_, lean_object* v_msgData_1625_, lean_object* v_severity_1626_, lean_object* v_isSilent_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v_severity_boxed_1633_; uint8_t v_isSilent_boxed_1634_; lean_object* v_res_1635_; 
v_severity_boxed_1633_ = lean_unbox(v_severity_1626_);
v_isSilent_boxed_1634_ = lean_unbox(v_isSilent_1627_);
v_res_1635_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1624_, v_msgData_1625_, v_severity_boxed_1633_, v_isSilent_boxed_1634_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v_ref_1624_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(lean_object* v_msgData_1636_, uint8_t v_severity_1637_, uint8_t v_isSilent_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_ref_1644_; lean_object* v___x_1645_; 
v_ref_1644_ = lean_ctor_get(v___y_1641_, 5);
v___x_1645_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33(v_ref_1644_, v_msgData_1636_, v_severity_1637_, v_isSilent_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32___boxed(lean_object* v_msgData_1646_, lean_object* v_severity_1647_, lean_object* v_isSilent_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v_severity_boxed_1654_; uint8_t v_isSilent_boxed_1655_; lean_object* v_res_1656_; 
v_severity_boxed_1654_ = lean_unbox(v_severity_1647_);
v_isSilent_boxed_1655_ = lean_unbox(v_isSilent_1648_);
v_res_1656_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1646_, v_severity_boxed_1654_, v_isSilent_boxed_1655_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(lean_object* v_msgData_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = 1;
v___x_1664_ = 0;
v___x_1665_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32(v_msgData_1657_, v___x_1663_, v___x_1664_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31___boxed(lean_object* v_msgData_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v_msgData_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(lean_object* v_opt_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_options_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_options_1676_ = lean_ctor_get(v___y_1674_, 2);
v___x_1677_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_1676_, v_opt_1673_);
v___x_1678_ = lean_box(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg___boxed(lean_object* v_opt_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_1681_, v___y_1682_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v_opt_1681_);
return v_res_1684_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__0));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__2));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(lean_object* v_id_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1721_; 
v___x_1697_ = lean_st_ref_get(v___y_1695_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1699_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1700_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v___x_1699_, v___y_1694_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1721_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1721_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v_isExporting_1710_; 
v_isExporting_1710_ = lean_ctor_get_uint8(v_env_1698_, sizeof(void*)*8);
lean_dec_ref(v_env_1698_);
if (v_isExporting_1710_ == 0)
{
lean_dec(v_a_1701_);
lean_dec(v_id_1691_);
goto v___jp_1705_;
}
else
{
lean_object* v_val_1711_; uint8_t v___x_1712_; 
v_val_1711_ = lean_ctor_get(v_a_1701_, 0);
lean_inc(v_val_1711_);
lean_dec(v_a_1701_);
v___x_1712_ = l_Lean_isPrivateName(v_id_1691_);
if (v___x_1712_ == 0)
{
lean_dec(v_val_1711_);
lean_dec(v_id_1691_);
goto v___jp_1705_;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_val_1711_);
lean_dec(v_val_1711_);
if (v___x_1713_ == 0)
{
lean_dec(v_id_1691_);
goto v___jp_1705_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_del_object(v___x_1703_);
v___x_1714_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_1715_ = 0;
v___x_1716_ = l_Lean_MessageData_ofConstName(v_id_1691_, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1714_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31(v___x_1719_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1720_;
}
}
}
v___jp_1705_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__31_spec__32_spec__33___closed__0));
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___boxed(lean_object* v_id_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_id_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(lean_object* v_id_1729_, uint8_t v_enableLog_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v_env_1737_; lean_object* v_options_1738_; lean_object* v_currNamespace_1739_; lean_object* v_openDecls_1740_; lean_object* v___x_1741_; lean_object* v_env_1742_; lean_object* v_res_1743_; 
v___x_1736_ = lean_st_ref_get(v___y_1734_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1736_);
v_options_1738_ = lean_ctor_get(v___y_1733_, 2);
v_currNamespace_1739_ = lean_ctor_get(v___y_1733_, 6);
v_openDecls_1740_ = lean_ctor_get(v___y_1733_, 7);
v___x_1741_ = lean_st_ref_get(v___y_1734_);
v_env_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_ref(v_env_1742_);
lean_dec(v___x_1741_);
lean_inc(v_openDecls_1740_);
lean_inc(v_currNamespace_1739_);
v_res_1743_ = l_Lean_ResolveName_resolveGlobalName(v_env_1737_, v_options_1738_, v_currNamespace_1739_, v_openDecls_1740_, v_id_1729_);
if (v_enableLog_1730_ == 0)
{
lean_dec_ref(v_env_1742_);
goto v___jp_1744_;
}
else
{
uint8_t v_isExporting_1747_; 
v_isExporting_1747_ = lean_ctor_get_uint8(v_env_1742_, sizeof(void*)*8);
lean_dec_ref(v_env_1742_);
if (v_isExporting_1747_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_1743_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v_fst_1750_; lean_object* v___x_1751_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_val_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v_fst_1750_ = lean_ctor_get(v_val_1749_, 0);
lean_inc(v_fst_1750_);
lean_dec(v_val_1749_);
v___x_1751_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28(v_fst_1750_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1760_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
if (lean_obj_tag(v_a_1752_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v_res_1743_);
v___x_1756_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
else
{
lean_dec_ref_known(v_a_1752_, 1);
lean_del_object(v___x_1754_);
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_res_1743_);
v_a_1761_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1751_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_dec(v___x_1748_);
goto v___jp_1744_;
}
}
}
v___jp_1744_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_res_1743_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24___boxed(lean_object* v_id_1769_, lean_object* v_enableLog_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
uint8_t v_enableLog_boxed_1776_; lean_object* v_res_1777_; 
v_enableLog_boxed_1776_ = lean_unbox(v_enableLog_1770_);
v_res_1777_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v_id_1769_, v_enableLog_boxed_1776_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(lean_object* v_n_u2080_1782_, lean_object* v_filter_1783_, lean_object* v_view_x3f_1784_, lean_object* v_n_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1861_; 
if (lean_obj_tag(v_view_x3f_1784_) == 1)
{
lean_object* v_val_1888_; lean_object* v_imported_1889_; lean_object* v_ctx_1890_; lean_object* v_scopes_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_val_1888_ = lean_ctor_get(v_view_x3f_1784_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v_view_x3f_1784_, 1);
v_imported_1889_ = lean_ctor_get(v_val_1888_, 1);
v_ctx_1890_ = lean_ctor_get(v_val_1888_, 2);
v_scopes_1891_ = lean_ctor_get(v_val_1888_, 3);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_val_1888_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_val_1888_, 0);
lean_dec(v_unused_1900_);
v___x_1893_ = v_val_1888_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_scopes_1891_);
lean_inc(v_ctx_1890_);
lean_inc(v_imported_1889_);
lean_dec(v_val_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_n_1785_);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_n_1785_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_imported_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_ctx_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_scopes_1891_);
v___x_1896_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_MacroScopesView_review(v___x_1896_);
v___y_1861_ = v___x_1897_;
goto v___jp_1860_;
}
}
}
else
{
lean_dec(v_view_x3f_1784_);
v___y_1861_ = v_n_1785_;
goto v___jp_1860_;
}
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
v___jp_1794_:
{
lean_object* v___x_1797_; 
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
v___x_1797_ = lean_apply_5(v___y_1796_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, lean_box(0));
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1817_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1817_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1817_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
if (lean_obj_tag(v_a_1798_) == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec(v___y_1795_);
v___x_1802_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
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
else
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_isSharedCheck_1815_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_a_1798_, 0);
lean_dec(v_unused_1816_);
v___x_1807_ = v_a_1798_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v_a_1798_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___y_1795_);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___y_1795_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1810_);
v___x_1812_ = v___x_1800_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v___y_1795_);
v_a_1818_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1797_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1797_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
v___jp_1826_:
{
lean_object* v___x_1829_; 
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
v___x_1829_ = lean_apply_5(v___y_1828_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, lean_box(0));
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1851_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1851_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1851_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
if (lean_obj_tag(v_a_1830_) == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v___y_1827_);
lean_dec_ref(v_filter_1783_);
v___x_1834_ = lean_box(0);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
else
{
lean_object* v___x_1838_; 
lean_dec_ref_known(v_a_1830_, 1);
lean_del_object(v___x_1832_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1827_);
v___x_1838_ = lean_apply_6(v_filter_1783_, v___y_1827_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, lean_box(0));
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; uint8_t v___x_1840_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___f_1841_; 
v___f_1841_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1795_ = v___y_1827_;
v___y_1796_ = v___f_1841_;
goto v___jp_1794_;
}
else
{
lean_object* v___f_1842_; 
v___f_1842_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1795_ = v___y_1827_;
v___y_1796_ = v___f_1842_;
goto v___jp_1794_;
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v___y_1827_);
v_a_1843_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1838_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1838_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v___y_1827_);
lean_dec_ref(v_filter_1783_);
v_a_1852_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1829_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1829_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
v___jp_1860_:
{
uint8_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = 0;
lean_inc(v___y_1861_);
v___x_1863_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24(v___y_1861_, v___x_1862_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1879_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1879_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1879_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
if (lean_obj_tag(v_a_1864_) == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec(v___y_1861_);
lean_dec_ref(v_filter_1783_);
v___x_1868_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
else
{
lean_object* v_val_1872_; 
lean_del_object(v___x_1866_);
v_val_1872_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_a_1864_, 1);
if (lean_obj_tag(v_val_1872_) == 1)
{
lean_object* v_head_1873_; lean_object* v_tail_1874_; 
v_head_1873_ = lean_ctor_get(v_val_1872_, 0);
lean_inc(v_head_1873_);
v_tail_1874_ = lean_ctor_get(v_val_1872_, 1);
lean_inc(v_tail_1874_);
lean_dec_ref_known(v_val_1872_, 2);
if (lean_obj_tag(v_tail_1874_) == 0)
{
lean_object* v_fst_1875_; uint8_t v___x_1876_; 
v_fst_1875_ = lean_ctor_get(v_head_1873_, 0);
lean_inc(v_fst_1875_);
lean_dec(v_head_1873_);
v___x_1876_ = lean_name_eq(v_fst_1875_, v_n_u2080_1782_);
lean_dec(v_fst_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___f_1877_; 
v___f_1877_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1827_ = v___y_1861_;
v___y_1828_ = v___f_1877_;
goto v___jp_1826_;
}
else
{
lean_object* v___f_1878_; 
v___f_1878_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1827_ = v___y_1861_;
v___y_1828_ = v___f_1878_;
goto v___jp_1826_;
}
}
else
{
lean_dec(v_tail_1874_);
lean_dec(v_head_1873_);
lean_dec(v___y_1861_);
lean_dec_ref(v_filter_1783_);
goto v___jp_1791_;
}
}
else
{
lean_dec(v_val_1872_);
lean_dec(v___y_1861_);
lean_dec_ref(v_filter_1783_);
goto v___jp_1791_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v___y_1861_);
lean_dec_ref(v_filter_1783_);
v_a_1880_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1863_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1863_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___boxed(lean_object* v_n_u2080_1901_, lean_object* v_filter_1902_, lean_object* v_view_x3f_1903_, lean_object* v_n_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_1901_, v_filter_1902_, v_view_x3f_1903_, v_n_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v_n_u2080_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(lean_object* v_n_u2080_1911_, lean_object* v_filter_1912_, lean_object* v_view_x3f_1913_, lean_object* v_as_x27_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
if (lean_obj_tag(v_as_x27_1914_) == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v_view_x3f_1913_);
lean_dec_ref(v_filter_1912_);
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_b_1915_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
else
{
lean_object* v_head_1923_; lean_object* v_tail_1924_; lean_object* v_snd_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1963_; 
v_head_1923_ = lean_ctor_get(v_as_x27_1914_, 0);
v_tail_1924_ = lean_ctor_get(v_as_x27_1914_, 1);
v_snd_1925_ = lean_ctor_get(v_b_1915_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_b_1915_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_b_1915_, 0);
lean_dec(v_unused_1964_);
v___x_1927_ = v_b_1915_;
v_isShared_1928_ = v_isSharedCheck_1963_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_snd_1925_);
lean_dec(v_b_1915_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1963_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = l_Lean_Name_appendCore(v_head_1923_, v_snd_1925_);
lean_inc(v___x_1929_);
lean_inc(v_view_x3f_1913_);
lean_inc_ref(v_filter_1912_);
v___x_1930_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_1911_, v_filter_1912_, v_view_x3f_1913_, v___x_1929_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1954_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1954_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1954_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
if (lean_obj_tag(v_a_1931_) == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_del_object(v___x_1933_);
v___x_1935_ = lean_box(0);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1929_);
lean_ctor_set(v___x_1927_, 0, v___x_1935_);
v___x_1937_ = v___x_1927_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1929_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v_as_x27_1914_ = v_tail_1924_;
v_b_1915_ = v___x_1937_;
goto _start;
}
}
else
{
lean_object* v___x_1941_; 
lean_dec(v_view_x3f_1913_);
lean_dec_ref(v_filter_1912_);
lean_inc_ref(v_a_1931_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1929_);
lean_ctor_set(v___x_1927_, 0, v_a_1931_);
v___x_1941_ = v___x_1927_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1929_);
v___x_1941_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1931_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_a_1931_, 0);
lean_dec(v_unused_1952_);
v___x_1943_ = v_a_1931_;
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v_a_1931_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1941_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1946_);
v___x_1948_ = v___x_1933_;
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
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___x_1929_);
lean_del_object(v___x_1927_);
lean_dec(v_view_x3f_1913_);
lean_dec_ref(v_filter_1912_);
v_a_1955_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1930_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1930_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg___boxed(lean_object* v_n_u2080_1965_, lean_object* v_filter_1966_, lean_object* v_view_x3f_1967_, lean_object* v_as_x27_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_1965_, v_filter_1966_, v_view_x3f_1967_, v_as_x27_1968_, v_b_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v_as_x27_1968_);
lean_dec(v_n_u2080_1965_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(lean_object* v_n_u2080_1979_, lean_object* v_filter_1980_, lean_object* v_view_x3f_1981_, lean_object* v_n_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___y_1989_; uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Name_hasMacroScopes(v_n_1982_);
if (v___x_2030_ == 0)
{
lean_object* v___f_2031_; 
v___f_2031_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__1));
v___y_1989_ = v___f_2031_;
goto v___jp_1988_;
}
else
{
lean_object* v___f_2032_; 
v___f_2032_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16___closed__0));
v___y_1989_ = v___f_2032_;
goto v___jp_1988_;
}
v___jp_1988_:
{
lean_object* v___x_1990_; 
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
v___x_1990_ = lean_apply_5(v___y_1989_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, lean_box(0));
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2021_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2021_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2021_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
if (lean_obj_tag(v_a_1991_) == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
lean_dec(v_n_1982_);
lean_dec(v_view_x3f_1981_);
lean_dec_ref(v_filter_1980_);
v___x_1995_ = lean_box(0);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref_known(v_a_1991_, 1);
lean_del_object(v___x_1993_);
v___x_1999_ = l_Lean_privateToUserName(v_n_1982_);
v___x_2000_ = l_Lean_Name_componentsRev(v___x_1999_);
v___x_2001_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___closed__0));
v___x_2002_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_1979_, v_filter_1980_, v_view_x3f_1981_, v___x_2000_, v___x_2001_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___x_2000_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2012_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_val_2007_; lean_object* v_fst_2008_; lean_object* v___x_2010_; 
v_val_2007_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_val_2007_);
lean_dec(v_a_2003_);
v_fst_2008_ = lean_ctor_get(v_val_2007_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_val_2007_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_fst_2008_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_fst_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_a_2013_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2002_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2002_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_n_1982_);
lean_dec(v_view_x3f_1981_);
lean_dec_ref(v_filter_1980_);
v_a_2022_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1990_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1990_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13___boxed(lean_object* v_n_u2080_2033_, lean_object* v_filter_2034_, lean_object* v_view_x3f_2035_, lean_object* v_n_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2033_, v_filter_2034_, v_view_x3f_2035_, v_n_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_n_u2080_2033_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(lean_object* v_n_u2080_2043_, lean_object* v_filter_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_array_get_size(v_as_2045_);
v___x_2053_ = lean_nat_dec_lt(v_i_2046_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_i_2046_);
lean_dec_ref(v_filter_2044_);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_array_fget_borrowed(v_as_2045_, v_i_2046_);
lean_inc(v___x_2057_);
lean_inc_ref(v_filter_2044_);
v___x_2058_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2043_, v_filter_2044_, v___x_2056_, v___x_2057_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
if (lean_obj_tag(v_a_2059_) == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_add(v_i_2046_, v___x_2060_);
lean_dec(v_i_2046_);
v_i_2046_ = v___x_2061_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_2059_, 1);
lean_dec(v_i_2046_);
lean_dec_ref(v_filter_2044_);
return v___x_2058_;
}
}
else
{
lean_dec(v_i_2046_);
lean_dec_ref(v_filter_2044_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14___boxed(lean_object* v_n_u2080_2063_, lean_object* v_filter_2064_, lean_object* v_as_2065_, lean_object* v_i_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2063_, v_filter_2064_, v_as_2065_, v_i_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec_ref(v_as_2065_);
lean_dec(v_n_u2080_2063_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(lean_object* v_n_u2081_2073_, lean_object* v_as_2074_, size_t v_i_2075_, size_t v_stop_2076_, lean_object* v_b_2077_){
_start:
{
lean_object* v___y_2079_; uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_eq(v_i_2075_, v_stop_2076_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2084_ = lean_array_uget_borrowed(v_as_2074_, v_i_2075_);
v___x_2085_ = l_Lean_Name_getPrefix(v___x_2084_);
v___x_2086_ = l_Lean_Name_getPrefix(v_n_u2081_2073_);
v___x_2087_ = l_Lean_Name_isPrefixOf(v___x_2085_, v___x_2086_);
lean_dec(v___x_2086_);
lean_dec(v___x_2085_);
if (v___x_2087_ == 0)
{
v___y_2079_ = v_b_2077_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2088_; 
lean_inc(v___x_2084_);
v___x_2088_ = lean_array_push(v_b_2077_, v___x_2084_);
v___y_2079_ = v___x_2088_;
goto v___jp_2078_;
}
}
else
{
return v_b_2077_;
}
v___jp_2078_:
{
size_t v___x_2080_; size_t v___x_2081_; 
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_add(v_i_2075_, v___x_2080_);
v_i_2075_ = v___x_2081_;
v_b_2077_ = v___y_2079_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15___boxed(lean_object* v_n_u2081_2089_, lean_object* v_as_2090_, lean_object* v_i_2091_, lean_object* v_stop_2092_, lean_object* v_b_2093_){
_start:
{
size_t v_i_boxed_2094_; size_t v_stop_boxed_2095_; lean_object* v_res_2096_; 
v_i_boxed_2094_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_stop_boxed_2095_ = lean_unbox_usize(v_stop_2092_);
lean_dec(v_stop_2092_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2089_, v_as_2090_, v_i_boxed_2094_, v_stop_boxed_2095_, v_b_2093_);
lean_dec_ref(v_as_2090_);
lean_dec(v_n_u2081_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(lean_object* v_n_u2080_2099_, uint8_t v_fullNames_2100_, uint8_t v_allowHorizAliases_2101_, lean_object* v_filter_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_view_2108_; lean_object* v_name_2109_; lean_object* v_n_u2081_2110_; 
lean_inc(v_n_u2080_2099_);
v_view_2108_ = l_Lean_extractMacroScopes(v_n_u2080_2099_);
v_name_2109_ = lean_ctor_get(v_view_2108_, 0);
lean_inc(v_name_2109_);
v_n_u2081_2110_ = l_Lean_privateToUserName(v_name_2109_);
if (v_fullNames_2100_ == 0)
{
lean_object* v___x_2111_; lean_object* v_aliases_2113_; lean_object* v_env_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2111_ = lean_st_ref_get(v___y_2106_);
v_env_2128_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2128_);
lean_dec(v___x_2111_);
lean_inc(v_n_u2080_2099_);
v___x_2129_ = l_Lean_getRevAliases(v_env_2128_, v_n_u2080_2099_);
v___x_2130_ = lean_array_mk(v___x_2129_);
if (v_allowHorizAliases_2101_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_array_get_size(v___x_2130_);
v___x_2133_ = ((lean_object*)(l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___closed__0));
v___x_2134_ = lean_nat_dec_lt(v___x_2131_, v___x_2132_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2130_);
v_aliases_2113_ = v___x_2133_;
goto v___jp_2112_;
}
else
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_le(v___x_2132_, v___x_2132_);
if (v___x_2135_ == 0)
{
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2130_);
v_aliases_2113_ = v___x_2133_;
goto v___jp_2112_;
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2132_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2110_, v___x_2130_, v___x_2136_, v___x_2137_, v___x_2133_);
lean_dec_ref(v___x_2130_);
v_aliases_2113_ = v___x_2138_;
goto v___jp_2112_;
}
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_of_nat(v___x_2132_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__15(v_n_u2081_2110_, v___x_2130_, v___x_2139_, v___x_2140_, v___x_2133_);
lean_dec_ref(v___x_2130_);
v_aliases_2113_ = v___x_2141_;
goto v___jp_2112_;
}
}
}
else
{
v_aliases_2113_ = v___x_2130_;
goto v___jp_2112_;
}
v___jp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_filter_2102_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__14(v_n_u2080_2099_, v_filter_2102_, v_aliases_2113_, v___x_2114_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec_ref(v_aliases_2113_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
if (lean_obj_tag(v_a_2116_) == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2126_; 
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___x_2115_, 0);
lean_dec(v_unused_2127_);
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 1);
lean_ctor_set(v___x_2118_, 0, v_view_2108_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_view_2108_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_rootNamespace;
v___x_2123_ = l_Lean_Name_append(v___x_2122_, v_n_u2081_2110_);
v___x_2124_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13(v_n_u2080_2099_, v_filter_2102_, v___x_2121_, v___x_2123_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v_n_u2080_2099_);
return v___x_2124_;
}
}
}
else
{
lean_dec_ref_known(v_a_2116_, 1);
lean_dec(v_n_u2081_2110_);
lean_dec_ref(v_view_2108_);
lean_dec_ref(v_filter_2102_);
lean_dec(v_n_u2080_2099_);
return v___x_2115_;
}
}
else
{
lean_dec(v_n_u2081_2110_);
lean_dec_ref(v_view_2108_);
lean_dec_ref(v_filter_2102_);
lean_dec(v_n_u2080_2099_);
return v___x_2115_;
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_view_2108_);
lean_inc(v_n_u2081_2110_);
lean_inc_ref(v___x_2142_);
lean_inc_ref(v_filter_2102_);
v___x_2143_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2099_, v_filter_2102_, v___x_2142_, v_n_u2081_2110_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = l_Lean_rootNamespace;
v___x_2146_ = l_Lean_Name_append(v___x_2145_, v_n_u2081_2110_);
v___x_2147_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16(v_n_u2080_2099_, v_filter_2102_, v___x_2142_, v___x_2146_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v_n_u2080_2099_);
return v___x_2147_;
}
else
{
lean_dec_ref_known(v_a_2144_, 1);
lean_dec_ref_known(v___x_2142_, 1);
lean_dec(v_n_u2081_2110_);
lean_dec_ref(v_filter_2102_);
lean_dec(v_n_u2080_2099_);
return v___x_2143_;
}
}
else
{
lean_dec_ref_known(v___x_2142_, 1);
lean_dec(v_n_u2081_2110_);
lean_dec_ref(v_filter_2102_);
lean_dec(v_n_u2080_2099_);
return v___x_2143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6___boxed(lean_object* v_n_u2080_2148_, lean_object* v_fullNames_2149_, lean_object* v_allowHorizAliases_2150_, lean_object* v_filter_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v_fullNames_boxed_2157_; uint8_t v_allowHorizAliases_boxed_2158_; lean_object* v_res_2159_; 
v_fullNames_boxed_2157_ = lean_unbox(v_fullNames_2149_);
v_allowHorizAliases_boxed_2158_ = lean_unbox(v_allowHorizAliases_2150_);
v_res_2159_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2148_, v_fullNames_boxed_2157_, v_allowHorizAliases_boxed_2158_, v_filter_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
if (lean_obj_tag(v_a_2160_) == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = l_List_reverse___redArg(v_a_2161_);
return v___x_2162_;
}
else
{
lean_object* v_head_2163_; lean_object* v_tail_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2175_; 
v_head_2163_ = lean_ctor_get(v_a_2160_, 0);
v_tail_2164_ = lean_ctor_get(v_a_2160_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2160_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2166_ = v_a_2160_;
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_tail_2164_);
lean_inc(v_head_2163_);
lean_dec(v_a_2160_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_snd_2168_; uint8_t v___x_2169_; 
v_snd_2168_ = lean_ctor_get(v_head_2163_, 1);
v___x_2169_ = l_List_isEmpty___redArg(v_snd_2168_);
if (v___x_2169_ == 0)
{
lean_del_object(v___x_2166_);
lean_dec(v_head_2163_);
v_a_2160_ = v_tail_2164_;
goto _start;
}
else
{
lean_object* v___x_2172_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v_a_2161_);
v___x_2172_ = v___x_2166_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_head_2163_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2161_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_a_2160_ = v_tail_2164_;
v_a_2161_ = v___x_2172_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_opt_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_options_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_options_2179_ = lean_ctor_get(v___y_2177_, 2);
v___x_2180_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_2179_, v_opt_2176_);
v___x_2181_ = lean_box(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_opt_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_2183_, v___y_2184_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_opt_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(lean_object* v_ref_2187_, lean_object* v_msgData_2188_, uint8_t v_severity_2189_, uint8_t v_isSilent_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; uint8_t v___y_2202_; uint8_t v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2233_; lean_object* v___y_2234_; uint8_t v___y_2235_; uint8_t v___y_2236_; uint8_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; uint8_t v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; uint8_t v___x_2280_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; uint8_t v___y_2285_; lean_object* v___y_2286_; uint8_t v___y_2287_; uint8_t v___y_2288_; uint8_t v___y_2290_; uint8_t v___x_2305_; 
v___x_2280_ = 2;
v___x_2305_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2189_, v___x_2280_);
if (v___x_2305_ == 0)
{
v___y_2290_ = v___x_2305_;
goto v___jp_2289_;
}
else
{
uint8_t v___x_2306_; 
lean_inc_ref(v_msgData_2188_);
v___x_2306_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2188_);
v___y_2290_ = v___x_2306_;
goto v___jp_2289_;
}
v___jp_2196_:
{
lean_object* v___x_2206_; lean_object* v_currNamespace_2207_; lean_object* v_openDecls_2208_; lean_object* v_env_2209_; lean_object* v_nextMacroScope_2210_; lean_object* v_ngen_2211_; lean_object* v_auxDeclNGen_2212_; lean_object* v_traceState_2213_; lean_object* v_cache_2214_; lean_object* v_messages_2215_; lean_object* v_infoState_2216_; lean_object* v_snapshotTasks_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2231_; 
v___x_2206_ = lean_st_ref_take(v___y_2205_);
v_currNamespace_2207_ = lean_ctor_get(v___y_2204_, 6);
v_openDecls_2208_ = lean_ctor_get(v___y_2204_, 7);
v_env_2209_ = lean_ctor_get(v___x_2206_, 0);
v_nextMacroScope_2210_ = lean_ctor_get(v___x_2206_, 1);
v_ngen_2211_ = lean_ctor_get(v___x_2206_, 2);
v_auxDeclNGen_2212_ = lean_ctor_get(v___x_2206_, 3);
v_traceState_2213_ = lean_ctor_get(v___x_2206_, 4);
v_cache_2214_ = lean_ctor_get(v___x_2206_, 5);
v_messages_2215_ = lean_ctor_get(v___x_2206_, 6);
v_infoState_2216_ = lean_ctor_get(v___x_2206_, 7);
v_snapshotTasks_2217_ = lean_ctor_get(v___x_2206_, 8);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2219_ = v___x_2206_;
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_snapshotTasks_2217_);
lean_inc(v_infoState_2216_);
lean_inc(v_messages_2215_);
lean_inc(v_cache_2214_);
lean_inc(v_traceState_2213_);
lean_inc(v_auxDeclNGen_2212_);
lean_inc(v_ngen_2211_);
lean_inc(v_nextMacroScope_2210_);
lean_inc(v_env_2209_);
lean_dec(v___x_2206_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_inc(v_openDecls_2208_);
lean_inc(v_currNamespace_2207_);
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_currNamespace_2207_);
lean_ctor_set(v___x_2221_, 1, v_openDecls_2208_);
v___x_2222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___y_2198_);
lean_inc_ref(v___y_2199_);
lean_inc_ref(v___y_2201_);
v___x_2223_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2223_, 0, v___y_2201_);
lean_ctor_set(v___x_2223_, 1, v___y_2197_);
lean_ctor_set(v___x_2223_, 2, v___y_2200_);
lean_ctor_set(v___x_2223_, 3, v___y_2199_);
lean_ctor_set(v___x_2223_, 4, v___x_2222_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*5, v___y_2202_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*5 + 1, v___y_2203_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*5 + 2, v_isSilent_2190_);
v___x_2224_ = l_Lean_MessageLog_add(v___x_2223_, v_messages_2215_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 6, v___x_2224_);
v___x_2226_ = v___x_2219_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_env_2209_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_nextMacroScope_2210_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_ngen_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_auxDeclNGen_2212_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_traceState_2213_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v_cache_2214_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v_infoState_2216_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_snapshotTasks_2217_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_st_ref_put(v___y_2205_, v___x_2226_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
}
v___jp_2232_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2256_; 
v___x_2241_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2188_);
v___x_2242_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10_spec__19(v___x_2241_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_inc_ref_n(v___y_2239_, 2);
v___x_2247_ = l_Lean_FileMap_toPosition(v___y_2239_, v___y_2238_);
lean_dec(v___y_2238_);
v___x_2248_ = l_Lean_FileMap_toPosition(v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_2235_ == 0)
{
lean_del_object(v___x_2245_);
lean_dec_ref(v___y_2233_);
v___y_2197_ = v___x_2247_;
v___y_2198_ = v_a_2243_;
v___y_2199_ = v___x_2250_;
v___y_2200_ = v___x_2249_;
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2193_;
v___y_2205_ = v___y_2194_;
goto v___jp_2196_;
}
else
{
uint8_t v___x_2251_; 
lean_inc(v_a_2243_);
v___x_2251_ = l_Lean_MessageData_hasTag(v___y_2233_, v_a_2243_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_dec_ref_known(v___x_2249_, 1);
lean_dec_ref(v___x_2247_);
lean_dec(v_a_2243_);
v___x_2252_ = lean_box(0);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2252_);
v___x_2254_ = v___x_2245_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_del_object(v___x_2245_);
v___y_2197_ = v___x_2247_;
v___y_2198_ = v_a_2243_;
v___y_2199_ = v___x_2250_;
v___y_2200_ = v___x_2249_;
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2193_;
v___y_2205_ = v___y_2194_;
goto v___jp_2196_;
}
}
}
}
v___jp_2257_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Syntax_getTailPos_x3f(v___y_2261_, v___y_2262_);
lean_dec(v___y_2261_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_inc(v___y_2265_);
v___y_2233_ = v___y_2258_;
v___y_2234_ = v___y_2259_;
v___y_2235_ = v___y_2260_;
v___y_2236_ = v___y_2262_;
v___y_2237_ = v___y_2263_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2264_;
v___y_2240_ = v___y_2265_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2267_; 
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___y_2233_ = v___y_2258_;
v___y_2234_ = v___y_2259_;
v___y_2235_ = v___y_2260_;
v___y_2236_ = v___y_2262_;
v___y_2237_ = v___y_2263_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2264_;
v___y_2240_ = v_val_2267_;
goto v___jp_2232_;
}
}
v___jp_2268_:
{
lean_object* v_ref_2276_; lean_object* v___x_2277_; 
v_ref_2276_ = l_Lean_replaceRef(v_ref_2187_, v___y_2270_);
v___x_2277_ = l_Lean_Syntax_getPos_x3f(v_ref_2276_, v___y_2273_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___y_2258_ = v___y_2269_;
v___y_2259_ = v___y_2271_;
v___y_2260_ = v___y_2272_;
v___y_2261_ = v_ref_2276_;
v___y_2262_ = v___y_2273_;
v___y_2263_ = v___y_2275_;
v___y_2264_ = v___y_2274_;
v___y_2265_ = v___x_2278_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2277_, 1);
v___y_2258_ = v___y_2269_;
v___y_2259_ = v___y_2271_;
v___y_2260_ = v___y_2272_;
v___y_2261_ = v_ref_2276_;
v___y_2262_ = v___y_2273_;
v___y_2263_ = v___y_2275_;
v___y_2264_ = v___y_2274_;
v___y_2265_ = v_val_2279_;
goto v___jp_2257_;
}
}
v___jp_2281_:
{
if (v___y_2288_ == 0)
{
v___y_2269_ = v___y_2282_;
v___y_2270_ = v___y_2283_;
v___y_2271_ = v___y_2284_;
v___y_2272_ = v___y_2285_;
v___y_2273_ = v___y_2287_;
v___y_2274_ = v___y_2286_;
v___y_2275_ = v_severity_2189_;
goto v___jp_2268_;
}
else
{
v___y_2269_ = v___y_2282_;
v___y_2270_ = v___y_2283_;
v___y_2271_ = v___y_2284_;
v___y_2272_ = v___y_2285_;
v___y_2273_ = v___y_2287_;
v___y_2274_ = v___y_2286_;
v___y_2275_ = v___x_2280_;
goto v___jp_2268_;
}
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
lean_object* v_fileName_2291_; lean_object* v_fileMap_2292_; lean_object* v_options_2293_; lean_object* v_ref_2294_; uint8_t v_suppressElabErrors_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___f_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; 
v_fileName_2291_ = lean_ctor_get(v___y_2193_, 0);
v_fileMap_2292_ = lean_ctor_get(v___y_2193_, 1);
v_options_2293_ = lean_ctor_get(v___y_2193_, 2);
v_ref_2294_ = lean_ctor_get(v___y_2193_, 5);
v_suppressElabErrors_2295_ = lean_ctor_get_uint8(v___y_2193_, sizeof(void*)*14 + 1);
v___x_2296_ = lean_box(v___y_2290_);
v___x_2297_ = lean_box(v_suppressElabErrors_2295_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2298_, 0, v___x_2296_);
lean_closure_set(v___f_2298_, 1, v___x_2297_);
v___x_2299_ = 1;
v___x_2300_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2189_, v___x_2299_);
if (v___x_2300_ == 0)
{
v___y_2282_ = v___f_2298_;
v___y_2283_ = v_ref_2294_;
v___y_2284_ = v_fileName_2291_;
v___y_2285_ = v_suppressElabErrors_2295_;
v___y_2286_ = v_fileMap_2292_;
v___y_2287_ = v___y_2290_;
v___y_2288_ = v___x_2300_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = l_Lean_warningAsError;
v___x_2302_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_2293_, v___x_2301_);
v___y_2282_ = v___f_2298_;
v___y_2283_ = v_ref_2294_;
v___y_2284_ = v_fileName_2291_;
v___y_2285_ = v_suppressElabErrors_2295_;
v___y_2286_ = v_fileMap_2292_;
v___y_2287_ = v___y_2290_;
v___y_2288_ = v___x_2302_;
goto v___jp_2281_;
}
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v_msgData_2188_);
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_ref_2307_, lean_object* v_msgData_2308_, lean_object* v_severity_2309_, lean_object* v_isSilent_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v_severity_boxed_2316_; uint8_t v_isSilent_boxed_2317_; lean_object* v_res_2318_; 
v_severity_boxed_2316_ = lean_unbox(v_severity_2309_);
v_isSilent_boxed_2317_ = lean_unbox(v_isSilent_2310_);
v_res_2318_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2307_, v_msgData_2308_, v_severity_boxed_2316_, v_isSilent_boxed_2317_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v_ref_2307_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(lean_object* v_msgData_2319_, uint8_t v_severity_2320_, uint8_t v_isSilent_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_ref_2327_; lean_object* v___x_2328_; 
v_ref_2327_ = lean_ctor_get(v___y_2324_, 5);
v___x_2328_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6_spec__10(v_ref_2327_, v_msgData_2319_, v_severity_2320_, v_isSilent_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_msgData_2329_, lean_object* v_severity_2330_, lean_object* v_isSilent_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_severity_boxed_2337_; uint8_t v_isSilent_boxed_2338_; lean_object* v_res_2339_; 
v_severity_boxed_2337_ = lean_unbox(v_severity_2330_);
v_isSilent_boxed_2338_ = lean_unbox(v_isSilent_2331_);
v_res_2339_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2329_, v_severity_boxed_2337_, v_isSilent_boxed_2338_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(lean_object* v_msgData_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = 1;
v___x_2347_ = 0;
v___x_2348_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3_spec__6(v_msgData_2340_, v___x_2346_, v___x_2347_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v_msgData_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(lean_object* v_id_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_env_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2385_; 
v___x_2362_ = lean_st_ref_get(v___y_2360_);
v_env_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_ref(v_env_2363_);
lean_dec(v___x_2362_);
v___x_2364_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_2365_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v___x_2364_, v___y_2359_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2385_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2385_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
uint8_t v_isExporting_2375_; 
v_isExporting_2375_ = lean_ctor_get_uint8(v_env_2363_, sizeof(void*)*8);
lean_dec_ref(v_env_2363_);
if (v_isExporting_2375_ == 0)
{
lean_dec(v_a_2366_);
lean_dec(v_id_2356_);
goto v___jp_2370_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Lean_isPrivateName(v_id_2356_);
if (v___x_2376_ == 0)
{
lean_dec(v_a_2366_);
lean_dec(v_id_2356_);
goto v___jp_2370_;
}
else
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_unbox(v_a_2366_);
lean_dec(v_a_2366_);
if (v___x_2377_ == 0)
{
lean_dec(v_id_2356_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_del_object(v___x_2368_);
v___x_2378_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__1);
v___x_2379_ = 0;
v___x_2380_ = l_Lean_MessageData_ofConstName(v_id_2356_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2378_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28___closed__3);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_2383_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2384_;
}
}
}
v___jp_2370_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_box(0);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2371_);
v___x_2373_ = v___x_2368_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1___boxed(lean_object* v_id_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_id_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(lean_object* v_id_2393_, uint8_t v_enableLog_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_env_2401_; lean_object* v_options_2402_; lean_object* v_currNamespace_2403_; lean_object* v_openDecls_2404_; lean_object* v___x_2405_; lean_object* v_env_2406_; lean_object* v_res_2407_; 
v___x_2400_ = lean_st_ref_get(v___y_2398_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2400_);
v_options_2402_ = lean_ctor_get(v___y_2397_, 2);
v_currNamespace_2403_ = lean_ctor_get(v___y_2397_, 6);
v_openDecls_2404_ = lean_ctor_get(v___y_2397_, 7);
v___x_2405_ = lean_st_ref_get(v___y_2398_);
v_env_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc_ref(v_env_2406_);
lean_dec(v___x_2405_);
lean_inc(v_openDecls_2404_);
lean_inc(v_currNamespace_2403_);
v_res_2407_ = l_Lean_ResolveName_resolveGlobalName(v_env_2401_, v_options_2402_, v_currNamespace_2403_, v_openDecls_2404_, v_id_2393_);
if (v_enableLog_2394_ == 0)
{
lean_object* v___x_2408_; 
lean_dec_ref(v_env_2406_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_res_2407_);
return v___x_2408_;
}
else
{
uint8_t v_isExporting_2409_; 
v_isExporting_2409_ = lean_ctor_get_uint8(v_env_2406_, sizeof(void*)*8);
lean_dec_ref(v_env_2406_);
if (v_isExporting_2409_ == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_res_2407_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; 
v___x_2411_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__0(v_res_2407_);
if (lean_obj_tag(v___x_2411_) == 1)
{
lean_object* v_val_2412_; lean_object* v_fst_2413_; lean_object* v___x_2414_; 
v_val_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_fst_2413_ = lean_ctor_get(v_val_2412_, 0);
lean_inc(v_fst_2413_);
lean_dec(v_val_2412_);
v___x_2414_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1(v_fst_2413_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v___x_2414_, 0);
lean_dec(v_unused_2422_);
v___x_2416_ = v___x_2414_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_dec(v___x_2414_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_res_2407_);
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_res_2407_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_res_2407_);
v_a_2423_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2414_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2414_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec(v___x_2411_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_res_2407_);
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0___boxed(lean_object* v_id_2432_, lean_object* v_enableLog_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
uint8_t v_enableLog_boxed_2439_; lean_object* v_res_2440_; 
v_enableLog_boxed_2439_ = lean_unbox(v_enableLog_2433_);
v_res_2440_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_id_2432_, v_enableLog_boxed_2439_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(lean_object* v_view_2441_, lean_object* v_findLocalDecl_x3f_2442_, lean_object* v_n_2443_, lean_object* v_projs_2444_, uint8_t v_globalDeclFound_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___y_2452_; lean_object* v___y_2453_; uint8_t v_globalDeclFoundNext_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_imported_2461_; lean_object* v_ctx_2462_; lean_object* v_scopes_2463_; lean_object* v_givenNameView_2464_; uint8_t v___y_2466_; 
v_imported_2461_ = lean_ctor_get(v_view_2441_, 1);
v_ctx_2462_ = lean_ctor_get(v_view_2441_, 2);
v_scopes_2463_ = lean_ctor_get(v_view_2441_, 3);
lean_inc(v_scopes_2463_);
lean_inc(v_ctx_2462_);
lean_inc(v_imported_2461_);
lean_inc(v_n_2443_);
v_givenNameView_2464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2464_, 0, v_n_2443_);
lean_ctor_set(v_givenNameView_2464_, 1, v_imported_2461_);
lean_ctor_set(v_givenNameView_2464_, 2, v_ctx_2462_);
lean_ctor_set(v_givenNameView_2464_, 3, v_scopes_2463_);
if (v_globalDeclFound_2445_ == 0)
{
v___y_2466_ = v_globalDeclFound_2445_;
goto v___jp_2465_;
}
else
{
uint8_t v___x_2501_; 
v___x_2501_ = l_List_isEmpty___redArg(v_projs_2444_);
if (v___x_2501_ == 0)
{
v___y_2466_ = v_globalDeclFound_2445_;
goto v___jp_2465_;
}
else
{
uint8_t v___x_2502_; 
v___x_2502_ = 0;
v___y_2466_ = v___x_2502_;
goto v___jp_2465_;
}
}
v___jp_2451_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___y_2453_);
lean_ctor_set(v___x_2459_, 1, v_projs_2444_);
v_n_2443_ = v___y_2452_;
v_projs_2444_ = v___x_2459_;
v_globalDeclFound_2445_ = v_globalDeclFoundNext_2454_;
v___y_2446_ = v___y_2455_;
v___y_2447_ = v___y_2456_;
v___y_2448_ = v___y_2457_;
v___y_2449_ = v___y_2458_;
goto _start;
}
v___jp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_box(v___y_2466_);
lean_inc_ref(v_findLocalDecl_x3f_2442_);
lean_inc_ref(v_givenNameView_2464_);
v___x_2468_ = lean_apply_2(v_findLocalDecl_x3f_2442_, v_givenNameView_2464_, v___x_2467_);
if (lean_obj_tag(v___x_2468_) == 0)
{
if (lean_obj_tag(v_n_2443_) == 1)
{
if (v_globalDeclFound_2445_ == 0)
{
lean_object* v_pre_2469_; lean_object* v_str_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_pre_2469_ = lean_ctor_get(v_n_2443_, 0);
lean_inc(v_pre_2469_);
v_str_2470_ = lean_ctor_get(v_n_2443_, 1);
lean_inc_ref(v_str_2470_);
lean_dec_ref_known(v_n_2443_, 2);
v___x_2471_ = l_Lean_MacroScopesView_review(v_givenNameView_2464_);
v___x_2472_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v___x_2471_, v_globalDeclFound_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; lean_object* v_r_2475_; uint8_t v___x_2476_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = lean_box(0);
v_r_2475_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11_spec__17(v_a_2473_, v___x_2474_);
v___x_2476_ = l_List_isEmpty___redArg(v_r_2475_);
lean_dec(v_r_2475_);
if (v___x_2476_ == 0)
{
uint8_t v_globalDeclFoundNext_2477_; 
v_globalDeclFoundNext_2477_ = 1;
v___y_2452_ = v_pre_2469_;
v___y_2453_ = v_str_2470_;
v_globalDeclFoundNext_2454_ = v_globalDeclFoundNext_2477_;
v___y_2455_ = v___y_2446_;
v___y_2456_ = v___y_2447_;
v___y_2457_ = v___y_2448_;
v___y_2458_ = v___y_2449_;
goto v___jp_2451_;
}
else
{
v___y_2452_ = v_pre_2469_;
v___y_2453_ = v_str_2470_;
v_globalDeclFoundNext_2454_ = v_globalDeclFound_2445_;
v___y_2455_ = v___y_2446_;
v___y_2456_ = v___y_2447_;
v___y_2457_ = v___y_2448_;
v___y_2458_ = v___y_2449_;
goto v___jp_2451_;
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_str_2470_);
lean_dec(v_pre_2469_);
lean_dec(v_projs_2444_);
lean_dec_ref(v_findLocalDecl_x3f_2442_);
v_a_2478_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2472_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2472_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_pre_2486_; lean_object* v_str_2487_; 
lean_dec_ref_known(v_givenNameView_2464_, 4);
v_pre_2486_ = lean_ctor_get(v_n_2443_, 0);
lean_inc(v_pre_2486_);
v_str_2487_ = lean_ctor_get(v_n_2443_, 1);
lean_inc_ref(v_str_2487_);
lean_dec_ref_known(v_n_2443_, 2);
v___y_2452_ = v_pre_2486_;
v___y_2453_ = v_str_2487_;
v_globalDeclFoundNext_2454_ = v_globalDeclFound_2445_;
v___y_2455_ = v___y_2446_;
v___y_2456_ = v___y_2447_;
v___y_2457_ = v___y_2448_;
v___y_2458_ = v___y_2449_;
goto v___jp_2451_;
}
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_dec_ref_known(v_givenNameView_2464_, 4);
lean_dec(v_projs_2444_);
lean_dec(v_n_2443_);
lean_dec_ref(v_findLocalDecl_x3f_2442_);
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
}
else
{
lean_object* v_val_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref_known(v_givenNameView_2464_, 4);
lean_dec(v_n_2443_);
lean_dec_ref(v_findLocalDecl_x3f_2442_);
v_val_2490_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2492_ = v___x_2468_;
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_val_2490_);
lean_dec(v___x_2468_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2494_ = l_Lean_LocalDecl_toExpr(v_val_2490_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v_projs_2444_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2495_);
v___x_2497_ = v___x_2492_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11___boxed(lean_object* v_view_2503_, lean_object* v_findLocalDecl_x3f_2504_, lean_object* v_n_2505_, lean_object* v_projs_2506_, lean_object* v_globalDeclFound_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v_globalDeclFound_boxed_2513_; lean_object* v_res_2514_; 
v_globalDeclFound_boxed_2513_ = lean_unbox(v_globalDeclFound_2507_);
v_res_2514_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2503_, v_findLocalDecl_x3f_2504_, v_n_2505_, v_projs_2506_, v_globalDeclFound_boxed_2513_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v_view_2503_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(lean_object* v_localDecl_2515_, lean_object* v_givenName_2516_){
_start:
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = l_Lean_LocalDecl_userName(v_localDecl_2515_);
v___x_2518_ = lean_name_eq(v___x_2517_, v_givenName_2516_);
lean_dec(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v_localDecl_2515_);
v___x_2519_ = lean_box(0);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_localDecl_2515_);
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_localDecl_2521_, lean_object* v_givenName_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_localDecl_2521_, v_givenName_2522_);
lean_dec(v_givenName_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(lean_object* v_t_2524_, lean_object* v_k_2525_){
_start:
{
if (lean_obj_tag(v_t_2524_) == 0)
{
lean_object* v_k_2526_; lean_object* v_v_2527_; lean_object* v_l_2528_; lean_object* v_r_2529_; uint8_t v___x_2530_; 
v_k_2526_ = lean_ctor_get(v_t_2524_, 1);
v_v_2527_ = lean_ctor_get(v_t_2524_, 2);
v_l_2528_ = lean_ctor_get(v_t_2524_, 3);
v_r_2529_ = lean_ctor_get(v_t_2524_, 4);
v___x_2530_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2525_, v_k_2526_);
switch(v___x_2530_)
{
case 0:
{
v_t_2524_ = v_l_2528_;
goto _start;
}
case 1:
{
lean_object* v___x_2532_; 
lean_inc(v_v_2527_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_v_2527_);
return v___x_2532_;
}
default: 
{
v_t_2524_ = v_r_2529_;
goto _start;
}
}
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_box(0);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_t_2535_, lean_object* v_k_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_2535_, v_k_2536_);
lean_dec(v_k_2536_);
lean_dec(v_t_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(lean_object* v_givenName_2538_, uint8_t v_skipAuxDecl_2539_, lean_object* v_auxDeclToFullName_2540_, lean_object* v___x_2541_, lean_object* v_givenNameView_2542_, lean_object* v_as_2543_, lean_object* v_i_2544_){
_start:
{
lean_object* v_zero_2545_; uint8_t v_isZero_2546_; 
v_zero_2545_ = lean_unsigned_to_nat(0u);
v_isZero_2546_ = lean_nat_dec_eq(v_i_2544_, v_zero_2545_);
if (v_isZero_2546_ == 1)
{
lean_object* v___x_2547_; 
lean_dec(v_i_2544_);
lean_dec_ref(v_givenNameView_2542_);
lean_dec(v___x_2541_);
v___x_2547_ = lean_box(0);
return v___x_2547_;
}
else
{
lean_object* v_one_2548_; lean_object* v_n_2549_; lean_object* v___y_2551_; lean_object* v___x_2553_; 
v_one_2548_ = lean_unsigned_to_nat(1u);
v_n_2549_ = lean_nat_sub(v_i_2544_, v_one_2548_);
lean_dec(v_i_2544_);
v___x_2553_ = lean_array_fget_borrowed(v_as_2543_, v_n_2549_);
if (lean_obj_tag(v___x_2553_) == 0)
{
v___y_2551_ = v___x_2553_;
goto v___jp_2550_;
}
else
{
lean_object* v_val_2554_; uint8_t v___x_2555_; 
v_val_2554_ = lean_ctor_get(v___x_2553_, 0);
v___x_2555_ = l_Lean_LocalDecl_isAuxDecl(v_val_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_inc(v_val_2554_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2554_, v_givenName_2538_);
v___y_2551_ = v___x_2556_;
goto v___jp_2550_;
}
else
{
if (v_skipAuxDecl_2539_ == 0)
{
if (v___x_2555_ == 0)
{
v_i_2544_ = v_n_2549_;
goto _start;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = l_Lean_LocalDecl_fvarId(v_val_2554_);
v___x_2559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_auxDeclToFullName_2540_, v___x_2558_);
lean_dec(v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v_fullDeclView_2561_; lean_object* v___y_2563_; lean_object* v_name_2584_; lean_object* v___x_2585_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_fullDeclView_2561_ = l_Lean_extractMacroScopes(v_val_2560_);
v_name_2584_ = lean_ctor_get(v_fullDeclView_2561_, 0);
lean_inc_n(v_name_2584_, 2);
v___x_2585_ = l_Lean_privateToUserName_x3f(v_name_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
v___y_2563_ = v_name_2584_;
goto v___jp_2562_;
}
else
{
lean_object* v_val_2586_; 
lean_dec(v_name_2584_);
v_val_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___y_2563_ = v_val_2586_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v_imported_2564_; lean_object* v_ctx_2565_; lean_object* v_scopes_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2582_; 
v_imported_2564_ = lean_ctor_get(v_fullDeclView_2561_, 1);
v_ctx_2565_ = lean_ctor_get(v_fullDeclView_2561_, 2);
v_scopes_2566_ = lean_ctor_get(v_fullDeclView_2561_, 3);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_fullDeclView_2561_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v_fullDeclView_2561_, 0);
lean_dec(v_unused_2583_);
v___x_2568_ = v_fullDeclView_2561_;
v_isShared_2569_ = v_isSharedCheck_2582_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_scopes_2566_);
lean_inc(v_ctx_2565_);
lean_inc(v_imported_2564_);
lean_dec(v_fullDeclView_2561_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2582_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fullDeclView_2571_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___y_2563_);
v_fullDeclView_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___y_2563_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_imported_2564_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_ctx_2565_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_scopes_2566_);
v_fullDeclView_2571_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v_fullDeclName_2572_; uint8_t v___x_2573_; 
lean_inc_ref(v_fullDeclView_2571_);
v_fullDeclName_2572_ = l_Lean_MacroScopesView_review(v_fullDeclView_2571_);
v___x_2573_ = l_Lean_Name_isPrefixOf(v___x_2541_, v_fullDeclName_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref(v_fullDeclView_2571_);
lean_inc(v___x_2541_);
lean_inc_ref(v_givenNameView_2542_);
lean_inc(v_val_2554_);
v___x_2574_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2554_, v_givenNameView_2542_, v_fullDeclName_2572_, v___x_2541_);
lean_dec(v_fullDeclName_2572_);
v___y_2551_ = v___x_2574_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2575_; lean_object* v_localDeclNameView_2576_; uint8_t v___x_2577_; 
lean_dec(v_fullDeclName_2572_);
v___x_2575_ = l_Lean_LocalDecl_userName(v_val_2554_);
v_localDeclNameView_2576_ = l_Lean_extractMacroScopes(v___x_2575_);
v___x_2577_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2576_, v_givenNameView_2542_);
lean_dec_ref(v_localDeclNameView_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v_fullDeclView_2571_);
v_i_2544_ = v_n_2549_;
goto _start;
}
else
{
uint8_t v___x_2579_; 
v___x_2579_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2542_, v_fullDeclView_2571_);
lean_dec_ref(v_fullDeclView_2571_);
if (v___x_2579_ == 0)
{
v_i_2544_ = v_n_2549_;
goto _start;
}
else
{
lean_inc_ref(v___x_2553_);
v___y_2551_ = v___x_2553_;
goto v___jp_2550_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2587_; 
lean_dec(v___x_2559_);
lean_inc(v_val_2554_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___lam__0(v_val_2554_, v_givenName_2538_);
v___y_2551_ = v___x_2587_;
goto v___jp_2550_;
}
}
}
else
{
v_i_2544_ = v_n_2549_;
goto _start;
}
}
}
v___jp_2550_:
{
if (lean_obj_tag(v___y_2551_) == 0)
{
v_i_2544_ = v_n_2549_;
goto _start;
}
else
{
lean_dec(v_n_2549_);
lean_dec_ref(v_givenNameView_2542_);
lean_dec(v___x_2541_);
return v___y_2551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg___boxed(lean_object* v_givenName_2589_, lean_object* v_skipAuxDecl_2590_, lean_object* v_auxDeclToFullName_2591_, lean_object* v___x_2592_, lean_object* v_givenNameView_2593_, lean_object* v_as_2594_, lean_object* v_i_2595_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2596_; lean_object* v_res_2597_; 
v_skipAuxDecl_boxed_2596_ = lean_unbox(v_skipAuxDecl_2590_);
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2589_, v_skipAuxDecl_boxed_2596_, v_auxDeclToFullName_2591_, v___x_2592_, v_givenNameView_2593_, v_as_2594_, v_i_2595_);
lean_dec_ref(v_as_2594_);
lean_dec(v_auxDeclToFullName_2591_);
lean_dec(v_givenName_2589_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(lean_object* v_givenName_2598_, uint8_t v_skipAuxDecl_2599_, lean_object* v_auxDeclToFullName_2600_, lean_object* v___x_2601_, lean_object* v_givenNameView_2602_, lean_object* v_as_2603_, lean_object* v_i_2604_){
_start:
{
lean_object* v_zero_2605_; uint8_t v_isZero_2606_; 
v_zero_2605_ = lean_unsigned_to_nat(0u);
v_isZero_2606_ = lean_nat_dec_eq(v_i_2604_, v_zero_2605_);
if (v_isZero_2606_ == 1)
{
lean_object* v___x_2607_; 
lean_dec(v_i_2604_);
lean_dec_ref(v_givenNameView_2602_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
return v___x_2607_;
}
else
{
lean_object* v_one_2608_; lean_object* v_n_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_one_2608_ = lean_unsigned_to_nat(1u);
v_n_2609_ = lean_nat_sub(v_i_2604_, v_one_2608_);
lean_dec(v_i_2604_);
v___x_2610_ = lean_array_fget_borrowed(v_as_2603_, v_n_2609_);
lean_inc_ref(v_givenNameView_2602_);
lean_inc(v___x_2601_);
v___x_2611_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2598_, v_skipAuxDecl_2599_, v_auxDeclToFullName_2600_, v___x_2601_, v_givenNameView_2602_, v___x_2610_);
if (lean_obj_tag(v___x_2611_) == 0)
{
v_i_2604_ = v_n_2609_;
goto _start;
}
else
{
lean_dec(v_n_2609_);
lean_dec_ref(v_givenNameView_2602_);
lean_dec(v___x_2601_);
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(lean_object* v_givenName_2613_, uint8_t v_skipAuxDecl_2614_, lean_object* v_auxDeclToFullName_2615_, lean_object* v___x_2616_, lean_object* v_givenNameView_2617_, lean_object* v_x_2618_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v_cs_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_cs_2619_ = lean_ctor_get(v_x_2618_, 0);
v___x_2620_ = lean_array_get_size(v_cs_2619_);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2613_, v_skipAuxDecl_2614_, v_auxDeclToFullName_2615_, v___x_2616_, v_givenNameView_2617_, v_cs_2619_, v___x_2620_);
return v___x_2621_;
}
else
{
lean_object* v_vs_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_vs_2622_ = lean_ctor_get(v_x_2618_, 0);
v___x_2623_ = lean_array_get_size(v_vs_2622_);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2613_, v_skipAuxDecl_2614_, v_auxDeclToFullName_2615_, v___x_2616_, v_givenNameView_2617_, v_vs_2622_, v___x_2623_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_givenName_2625_, lean_object* v_skipAuxDecl_2626_, lean_object* v_auxDeclToFullName_2627_, lean_object* v___x_2628_, lean_object* v_givenNameView_2629_, lean_object* v_x_2630_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2631_; lean_object* v_res_2632_; 
v_skipAuxDecl_boxed_2631_ = lean_unbox(v_skipAuxDecl_2626_);
v_res_2632_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2625_, v_skipAuxDecl_boxed_2631_, v_auxDeclToFullName_2627_, v___x_2628_, v_givenNameView_2629_, v_x_2630_);
lean_dec_ref(v_x_2630_);
lean_dec(v_auxDeclToFullName_2627_);
lean_dec(v_givenName_2625_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg___boxed(lean_object* v_givenName_2633_, lean_object* v_skipAuxDecl_2634_, lean_object* v_auxDeclToFullName_2635_, lean_object* v___x_2636_, lean_object* v_givenNameView_2637_, lean_object* v_as_2638_, lean_object* v_i_2639_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2640_; lean_object* v_res_2641_; 
v_skipAuxDecl_boxed_2640_ = lean_unbox(v_skipAuxDecl_2634_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_2633_, v_skipAuxDecl_boxed_2640_, v_auxDeclToFullName_2635_, v___x_2636_, v_givenNameView_2637_, v_as_2638_, v_i_2639_);
lean_dec_ref(v_as_2638_);
lean_dec(v_auxDeclToFullName_2635_);
lean_dec(v_givenName_2633_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(lean_object* v_givenName_2642_, uint8_t v_skipAuxDecl_2643_, lean_object* v_auxDeclToFullName_2644_, lean_object* v___x_2645_, lean_object* v_givenNameView_2646_, lean_object* v_t_2647_){
_start:
{
lean_object* v_root_2648_; lean_object* v_tail_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_root_2648_ = lean_ctor_get(v_t_2647_, 0);
v_tail_2649_ = lean_ctor_get(v_t_2647_, 1);
v___x_2650_ = lean_array_get_size(v_tail_2649_);
lean_inc_ref(v_givenNameView_2646_);
lean_inc(v___x_2645_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2642_, v_skipAuxDecl_2643_, v_auxDeclToFullName_2644_, v___x_2645_, v_givenNameView_2646_, v_tail_2649_, v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12(v_givenName_2642_, v_skipAuxDecl_2643_, v_auxDeclToFullName_2644_, v___x_2645_, v_givenNameView_2646_, v_root_2648_);
return v___x_2652_;
}
else
{
lean_dec_ref(v_givenNameView_2646_);
lean_dec(v___x_2645_);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9___boxed(lean_object* v_givenName_2653_, lean_object* v_skipAuxDecl_2654_, lean_object* v_auxDeclToFullName_2655_, lean_object* v___x_2656_, lean_object* v_givenNameView_2657_, lean_object* v_t_2658_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2659_; lean_object* v_res_2660_; 
v_skipAuxDecl_boxed_2659_ = lean_unbox(v_skipAuxDecl_2654_);
v_res_2660_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2653_, v_skipAuxDecl_boxed_2659_, v_auxDeclToFullName_2655_, v___x_2656_, v_givenNameView_2657_, v_t_2658_);
lean_dec_ref(v_t_2658_);
lean_dec(v_auxDeclToFullName_2655_);
lean_dec(v_givenName_2653_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(lean_object* v_localDecl_x3f_2661_, lean_object* v_givenName_2662_, lean_object* v_as_2663_, lean_object* v_i_2664_){
_start:
{
lean_object* v_zero_2665_; uint8_t v_isZero_2666_; 
v_zero_2665_ = lean_unsigned_to_nat(0u);
v_isZero_2666_ = lean_nat_dec_eq(v_i_2664_, v_zero_2665_);
if (v_isZero_2666_ == 1)
{
lean_object* v___x_2667_; 
lean_dec(v_i_2664_);
v___x_2667_ = lean_box(0);
return v___x_2667_;
}
else
{
lean_object* v_one_2668_; lean_object* v_n_2669_; lean_object* v___y_2671_; lean_object* v___x_2673_; 
v_one_2668_ = lean_unsigned_to_nat(1u);
v_n_2669_ = lean_nat_sub(v_i_2664_, v_one_2668_);
lean_dec(v_i_2664_);
v___x_2673_ = lean_array_fget_borrowed(v_as_2663_, v_n_2669_);
if (lean_obj_tag(v___x_2673_) == 0)
{
v___y_2671_ = v___x_2673_;
goto v___jp_2670_;
}
else
{
lean_object* v_val_2674_; uint8_t v___x_2675_; 
v_val_2674_ = lean_ctor_get(v___x_2673_, 0);
v___x_2675_ = l_Lean_LocalDecl_isAuxDecl(v_val_2674_);
if (v___x_2675_ == 0)
{
v___y_2671_ = v_localDecl_x3f_2661_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = l_Lean_LocalDecl_userName(v_val_2674_);
v___x_2677_ = lean_name_eq(v___x_2676_, v_givenName_2662_);
lean_dec(v___x_2676_);
if (v___x_2677_ == 0)
{
v_i_2664_ = v_n_2669_;
goto _start;
}
else
{
v___y_2671_ = v___x_2673_;
goto v___jp_2670_;
}
}
}
v___jp_2670_:
{
if (lean_obj_tag(v___y_2671_) == 0)
{
v_i_2664_ = v_n_2669_;
goto _start;
}
else
{
lean_dec(v_n_2669_);
lean_inc_ref(v___y_2671_);
return v___y_2671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_localDecl_x3f_2679_, lean_object* v_givenName_2680_, lean_object* v_as_2681_, lean_object* v_i_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2679_, v_givenName_2680_, v_as_2681_, v_i_2682_);
lean_dec_ref(v_as_2681_);
lean_dec(v_givenName_2680_);
lean_dec(v_localDecl_x3f_2679_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(lean_object* v_localDecl_x3f_2684_, lean_object* v_givenName_2685_, lean_object* v_as_2686_, lean_object* v_i_2687_){
_start:
{
lean_object* v_zero_2688_; uint8_t v_isZero_2689_; 
v_zero_2688_ = lean_unsigned_to_nat(0u);
v_isZero_2689_ = lean_nat_dec_eq(v_i_2687_, v_zero_2688_);
if (v_isZero_2689_ == 1)
{
lean_object* v___x_2690_; 
lean_dec(v_i_2687_);
v___x_2690_ = lean_box(0);
return v___x_2690_;
}
else
{
lean_object* v_one_2691_; lean_object* v_n_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_one_2691_ = lean_unsigned_to_nat(1u);
v_n_2692_ = lean_nat_sub(v_i_2687_, v_one_2691_);
lean_dec(v_i_2687_);
v___x_2693_ = lean_array_fget_borrowed(v_as_2686_, v_n_2692_);
v___x_2694_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2684_, v_givenName_2685_, v___x_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
v_i_2687_ = v_n_2692_;
goto _start;
}
else
{
lean_dec(v_n_2692_);
return v___x_2694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(lean_object* v_localDecl_x3f_2696_, lean_object* v_givenName_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2698_) == 0)
{
lean_object* v_cs_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_cs_2699_ = lean_ctor_get(v_x_2698_, 0);
v___x_2700_ = lean_array_get_size(v_cs_2699_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2696_, v_givenName_2697_, v_cs_2699_, v___x_2700_);
return v___x_2701_;
}
else
{
lean_object* v_vs_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_vs_2702_ = lean_ctor_get(v_x_2698_, 0);
v___x_2703_ = lean_array_get_size(v_vs_2702_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2696_, v_givenName_2697_, v_vs_2702_, v___x_2703_);
return v___x_2704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15___boxed(lean_object* v_localDecl_x3f_2705_, lean_object* v_givenName_2706_, lean_object* v_x_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2705_, v_givenName_2706_, v_x_2707_);
lean_dec_ref(v_x_2707_);
lean_dec(v_givenName_2706_);
lean_dec(v_localDecl_x3f_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg___boxed(lean_object* v_localDecl_x3f_2709_, lean_object* v_givenName_2710_, lean_object* v_as_2711_, lean_object* v_i_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_2709_, v_givenName_2710_, v_as_2711_, v_i_2712_);
lean_dec_ref(v_as_2711_);
lean_dec(v_givenName_2710_);
lean_dec(v_localDecl_x3f_2709_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(lean_object* v_localDecl_x3f_2714_, lean_object* v_givenName_2715_, lean_object* v_t_2716_){
_start:
{
lean_object* v_root_2717_; lean_object* v_tail_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_root_2717_ = lean_ctor_get(v_t_2716_, 0);
v_tail_2718_ = lean_ctor_get(v_t_2716_, 1);
v___x_2719_ = lean_array_get_size(v_tail_2718_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_2714_, v_givenName_2715_, v_tail_2718_, v___x_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15(v_localDecl_x3f_2714_, v_givenName_2715_, v_root_2717_);
return v___x_2721_;
}
else
{
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10___boxed(lean_object* v_localDecl_x3f_2722_, lean_object* v_givenName_2723_, lean_object* v_t_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2722_, v_givenName_2723_, v_t_2724_);
lean_dec_ref(v_t_2724_);
lean_dec(v_givenName_2723_);
lean_dec(v_localDecl_x3f_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(lean_object* v_auxDeclToFullName_2726_, lean_object* v_currNamespace_2727_, lean_object* v_decls_2728_, lean_object* v_givenNameView_2729_, uint8_t v_skipAuxDecl_2730_){
_start:
{
lean_object* v_givenName_2731_; lean_object* v_localDecl_x3f_2732_; 
lean_inc_ref(v_givenNameView_2729_);
v_givenName_2731_ = l_Lean_MacroScopesView_review(v_givenNameView_2729_);
v_localDecl_x3f_2732_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9(v_givenName_2731_, v_skipAuxDecl_2730_, v_auxDeclToFullName_2726_, v_currNamespace_2727_, v_givenNameView_2729_, v_decls_2728_);
if (lean_obj_tag(v_localDecl_x3f_2732_) == 0)
{
if (v_skipAuxDecl_2730_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10(v_localDecl_x3f_2732_, v_givenName_2731_, v_decls_2728_);
lean_dec(v_givenName_2731_);
return v___x_2733_;
}
else
{
lean_dec(v_givenName_2731_);
return v_localDecl_x3f_2732_;
}
}
else
{
lean_dec(v_givenName_2731_);
return v_localDecl_x3f_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_2734_, lean_object* v_currNamespace_2735_, lean_object* v_decls_2736_, lean_object* v_givenNameView_2737_, lean_object* v_skipAuxDecl_2738_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2739_; lean_object* v_res_2740_; 
v_skipAuxDecl_boxed_2739_ = lean_unbox(v_skipAuxDecl_2738_);
v_res_2740_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0(v_auxDeclToFullName_2734_, v_currNamespace_2735_, v_decls_2736_, v_givenNameView_2737_, v_skipAuxDecl_boxed_2739_);
lean_dec_ref(v_decls_2736_);
lean_dec(v_auxDeclToFullName_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(lean_object* v_n_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_lctx_2747_; lean_object* v_decls_2748_; lean_object* v_auxDeclToFullName_2749_; lean_object* v_currNamespace_2750_; lean_object* v_view_2751_; lean_object* v_name_2752_; lean_object* v_findLocalDecl_x3f_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v_lctx_2747_ = lean_ctor_get(v___y_2742_, 2);
v_decls_2748_ = lean_ctor_get(v_lctx_2747_, 1);
v_auxDeclToFullName_2749_ = lean_ctor_get(v_lctx_2747_, 2);
v_currNamespace_2750_ = lean_ctor_get(v___y_2744_, 6);
v_view_2751_ = l_Lean_extractMacroScopes(v_n_2741_);
v_name_2752_ = lean_ctor_get(v_view_2751_, 0);
lean_inc(v_name_2752_);
lean_inc_ref(v_decls_2748_);
lean_inc(v_currNamespace_2750_);
lean_inc(v_auxDeclToFullName_2749_);
v_findLocalDecl_x3f_2753_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_2753_, 0, v_auxDeclToFullName_2749_);
lean_closure_set(v_findLocalDecl_x3f_2753_, 1, v_currNamespace_2750_);
lean_closure_set(v_findLocalDecl_x3f_2753_, 2, v_decls_2748_);
v___x_2754_ = lean_box(0);
v___x_2755_ = 0;
v___x_2756_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__11(v_view_2751_, v_findLocalDecl_x3f_2753_, v_name_2752_, v___x_2754_, v___x_2755_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec_ref(v_view_2751_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5___boxed(lean_object* v_n_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(uint8_t v___x_2764_, lean_object* v_n_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5(v_n_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2785_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2785_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2785_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
if (lean_obj_tag(v_a_2772_) == 0)
{
uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2776_ = 1;
v___x_2777_ = lean_box(v___x_2776_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
lean_dec_ref_known(v_a_2772_, 1);
v___x_2781_ = lean_box(v___x_2764_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2781_);
v___x_2783_ = v___x_2774_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2771_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2771_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0___boxed(lean_object* v___x_2794_, lean_object* v_n_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v___x_27606__boxed_2801_; lean_object* v_res_2802_; 
v___x_27606__boxed_2801_ = lean_unbox(v___x_2794_);
v_res_2802_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___lam__0(v___x_27606__boxed_2801_, v_n_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(lean_object* v_n_u2080_2806_, uint8_t v_fullNames_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
uint8_t v___x_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; 
v___x_2813_ = 0;
v___f_2814_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___closed__0));
v___x_2815_ = l_Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6(v_n_u2080_2806_, v_fullNames_2807_, v___x_2813_, v___f_2814_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2___boxed(lean_object* v_n_u2080_2816_, lean_object* v_fullNames_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_fullNames_boxed_2823_; lean_object* v_res_2824_; 
v_fullNames_boxed_2823_ = lean_unbox(v_fullNames_2817_);
v_res_2824_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_n_u2080_2816_, v_fullNames_boxed_2823_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2824_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(lean_object* v_x_2825_, lean_object* v_x_2826_){
_start:
{
if (lean_obj_tag(v_x_2825_) == 0)
{
if (lean_obj_tag(v_x_2826_) == 0)
{
uint8_t v___x_2827_; 
v___x_2827_ = 1;
return v___x_2827_;
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = 0;
return v___x_2828_;
}
}
else
{
if (lean_obj_tag(v_x_2826_) == 0)
{
uint8_t v___x_2829_; 
v___x_2829_ = 0;
return v___x_2829_;
}
else
{
lean_object* v_head_2830_; lean_object* v_tail_2831_; lean_object* v_head_2832_; lean_object* v_tail_2833_; uint8_t v___x_2834_; 
v_head_2830_ = lean_ctor_get(v_x_2825_, 0);
v_tail_2831_ = lean_ctor_get(v_x_2825_, 1);
v_head_2832_ = lean_ctor_get(v_x_2826_, 0);
v_tail_2833_ = lean_ctor_get(v_x_2826_, 1);
v___x_2834_ = lean_string_dec_eq(v_head_2830_, v_head_2832_);
if (v___x_2834_ == 0)
{
return v___x_2834_;
}
else
{
v_x_2825_ = v_tail_2831_;
v_x_2826_ = v_tail_2833_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3___boxed(lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
uint8_t v_res_2838_; lean_object* v_r_2839_; 
v_res_2838_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_x_2836_, v_x_2837_);
lean_dec(v_x_2837_);
lean_dec(v_x_2836_);
v_r_2839_ = lean_box(v_res_2838_);
return v_r_2839_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(lean_object* v_x_2840_, lean_object* v_x_2841_){
_start:
{
if (lean_obj_tag(v_x_2840_) == 0)
{
if (lean_obj_tag(v_x_2841_) == 0)
{
uint8_t v___x_2842_; 
v___x_2842_ = 1;
return v___x_2842_;
}
else
{
uint8_t v___x_2843_; 
v___x_2843_ = 0;
return v___x_2843_;
}
}
else
{
if (lean_obj_tag(v_x_2841_) == 0)
{
uint8_t v___x_2844_; 
v___x_2844_ = 0;
return v___x_2844_;
}
else
{
lean_object* v_head_2845_; lean_object* v_tail_2846_; lean_object* v_head_2847_; lean_object* v_tail_2848_; uint8_t v___y_2850_; lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v_fst_2854_; lean_object* v_snd_2855_; uint8_t v___x_2856_; 
v_head_2845_ = lean_ctor_get(v_x_2840_, 0);
v_tail_2846_ = lean_ctor_get(v_x_2840_, 1);
v_head_2847_ = lean_ctor_get(v_x_2841_, 0);
v_tail_2848_ = lean_ctor_get(v_x_2841_, 1);
v_fst_2852_ = lean_ctor_get(v_head_2845_, 0);
v_snd_2853_ = lean_ctor_get(v_head_2845_, 1);
v_fst_2854_ = lean_ctor_get(v_head_2847_, 0);
v_snd_2855_ = lean_ctor_get(v_head_2847_, 1);
v___x_2856_ = lean_name_eq(v_fst_2852_, v_fst_2854_);
if (v___x_2856_ == 0)
{
v___y_2850_ = v___x_2856_;
goto v___jp_2849_;
}
else
{
uint8_t v___x_2857_; 
v___x_2857_ = l_List_beq___at___00List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1_spec__3(v_snd_2853_, v_snd_2855_);
v___y_2850_ = v___x_2857_;
goto v___jp_2849_;
}
v___jp_2849_:
{
if (v___y_2850_ == 0)
{
return v___y_2850_;
}
else
{
v_x_2840_ = v_tail_2846_;
v_x_2841_ = v_tail_2848_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1___boxed(lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
uint8_t v_res_2860_; lean_object* v_r_2861_; 
v_res_2860_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_x_2858_, v_x_2859_);
lean_dec(v_x_2859_);
lean_dec(v_x_2858_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__0));
v___x_2864_ = l_Lean_stringToMessageData(v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(lean_object* v_declName_2865_, lean_object* v_newName_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_ref_2872_; 
v_ref_2872_ = lean_ctor_get(v_a_2869_, 5);
if (lean_obj_tag(v_ref_2872_) == 3)
{
lean_object* v_val_2873_; uint8_t v___x_2874_; 
v_val_2873_ = lean_ctor_get(v_ref_2872_, 2);
v___x_2874_ = l_Lean_Name_hasMacroScopes(v_val_2873_);
if (v___x_2874_ == 0)
{
uint8_t v___x_2875_; lean_object* v___x_2953_; 
v___x_2875_ = 1;
v___x_2953_ = l_Lean_Syntax_getRange_x3f(v_ref_2872_, v___x_2875_);
if (lean_obj_tag(v___x_2953_) == 0)
{
if (v___x_2874_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec(v_newName_2866_);
lean_dec(v_declName_2865_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
else
{
goto v___jp_2876_;
}
}
else
{
lean_dec_ref_known(v___x_2953_, 1);
goto v___jp_2876_;
}
v___jp_2876_:
{
lean_object* v___x_2877_; 
lean_inc(v_val_2873_);
v___x_2877_ = l_Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0(v_val_2873_, v___x_2875_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2944_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2944_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2944_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_declName_2865_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v___x_2882_);
v___x_2885_ = l_List_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__1(v_a_2878_, v___x_2884_);
lean_dec_ref_known(v___x_2884_, 2);
lean_dec(v_a_2878_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_newName_2866_);
v___x_2886_ = lean_box(0);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2886_);
v___x_2888_ = v___x_2880_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
else
{
lean_object* v___x_2890_; 
lean_del_object(v___x_2880_);
v___x_2890_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2(v_newName_2866_, v___x_2874_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2935_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2935_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2935_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
if (lean_obj_tag(v_a_2891_) == 1)
{
lean_object* v_val_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2930_; 
lean_del_object(v___x_2893_);
v_val_2895_ = lean_ctor_get(v_a_2891_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_a_2891_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2897_ = v_a_2891_;
v_isShared_2898_ = v_isSharedCheck_2930_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_val_2895_);
lean_dec(v_a_2891_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2930_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1_once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___closed__1);
v___x_2900_ = l_Lean_Name_toString(v_val_2895_, v___x_2875_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
lean_ctor_set(v___x_2903_, 2, v___x_2902_);
lean_ctor_set(v___x_2903_, 3, v___x_2902_);
lean_ctor_set(v___x_2903_, 4, v___x_2902_);
lean_ctor_set(v___x_2903_, 5, v___x_2902_);
v___x_2904_ = 0;
v___x_2905_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2902_);
lean_ctor_set(v___x_2905_, 2, v___x_2902_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*3, v___x_2904_);
v___x_2906_ = lean_unsigned_to_nat(1u);
v___x_2907_ = lean_mk_empty_array_with_capacity(v___x_2906_);
v___x_2908_ = lean_array_push(v___x_2907_, v___x_2905_);
lean_inc_ref(v_ref_2872_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_ref_2872_);
v___x_2910_ = v___x_2897_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_ref_2872_);
v___x_2910_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_MessageData_hint(v___x_2899_, v___x_2908_, v___x_2910_, v___x_2902_, v___x_2874_, v_a_2869_, v_a_2870_);
lean_dec_ref(v___x_2908_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2911_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2911_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
lean_dec(v_a_2891_);
v___x_2931_ = lean_box(0);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2931_);
v___x_2933_ = v___x_2893_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_a_2936_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2890_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2890_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_newName_2866_);
lean_dec(v_declName_2865_);
v_a_2945_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2877_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2877_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v_newName_2866_);
lean_dec(v_declName_2865_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec(v_newName_2866_);
lean_dec(v_declName_2865_);
v___x_2958_ = lean_box(0);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f___boxed(lean_object* v_declName_2960_, lean_object* v_newName_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_2960_, v_newName_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(lean_object* v_opt_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___redArg(v_opt_2968_, v___y_2971_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_opt_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__2(v_opt_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_opt_2975_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(lean_object* v_00_u03b4_2982_, lean_object* v_t_2983_, lean_object* v_k_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___redArg(v_t_2983_, v_k_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b4_2986_, lean_object* v_t_2987_, lean_object* v_k_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__8(v_00_u03b4_2986_, v_t_2987_, v_k_2988_);
lean_dec(v_k_2988_);
lean_dec(v_t_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(lean_object* v_givenName_2990_, uint8_t v_skipAuxDecl_2991_, lean_object* v_auxDeclToFullName_2992_, lean_object* v___x_2993_, lean_object* v_givenNameView_2994_, lean_object* v_as_2995_, lean_object* v_i_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___redArg(v_givenName_2990_, v_skipAuxDecl_2991_, v_auxDeclToFullName_2992_, v___x_2993_, v_givenNameView_2994_, v_as_2995_, v_i_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_givenName_2999_, lean_object* v_skipAuxDecl_3000_, lean_object* v_auxDeclToFullName_3001_, lean_object* v___x_3002_, lean_object* v_givenNameView_3003_, lean_object* v_as_3004_, lean_object* v_i_3005_, lean_object* v_a_3006_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3007_; lean_object* v_res_3008_; 
v_skipAuxDecl_boxed_3007_ = lean_unbox(v_skipAuxDecl_3000_);
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__11(v_givenName_2999_, v_skipAuxDecl_boxed_3007_, v_auxDeclToFullName_3001_, v___x_3002_, v_givenNameView_3003_, v_as_3004_, v_i_3005_, v_a_3006_);
lean_dec_ref(v_as_3004_);
lean_dec(v_auxDeclToFullName_3001_);
lean_dec(v_givenName_2999_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(lean_object* v_localDecl_x3f_3009_, lean_object* v_givenName_3010_, lean_object* v_as_3011_, lean_object* v_i_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___redArg(v_localDecl_x3f_3009_, v_givenName_3010_, v_as_3011_, v_i_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14___boxed(lean_object* v_localDecl_x3f_3015_, lean_object* v_givenName_3016_, lean_object* v_as_3017_, lean_object* v_i_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__14(v_localDecl_x3f_3015_, v_givenName_3016_, v_as_3017_, v_i_3018_, v_a_3019_);
lean_dec_ref(v_as_3017_);
lean_dec(v_givenName_3016_);
lean_dec(v_localDecl_x3f_3015_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(lean_object* v_n_u2080_3021_, lean_object* v_filter_3022_, lean_object* v_view_x3f_3023_, lean_object* v_as_3024_, lean_object* v_as_x27_3025_, lean_object* v_b_3026_, lean_object* v_a_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___redArg(v_n_u2080_3021_, v_filter_3022_, v_view_x3f_3023_, v_as_x27_3025_, v_b_3026_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_n_u2080_3034_, lean_object* v_filter_3035_, lean_object* v_view_x3f_3036_, lean_object* v_as_3037_, lean_object* v_as_x27_3038_, lean_object* v_b_3039_, lean_object* v_a_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_List_forIn_x27_loop___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__13_spec__20(v_n_u2080_3034_, v_filter_3035_, v_view_x3f_3036_, v_as_3037_, v_as_x27_3038_, v_b_3039_, v_a_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v_as_x27_3038_);
lean_dec(v_as_3037_);
lean_dec(v_n_u2080_3034_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(lean_object* v_givenName_3047_, uint8_t v_skipAuxDecl_3048_, lean_object* v_auxDeclToFullName_3049_, lean_object* v___x_3050_, lean_object* v_givenNameView_3051_, lean_object* v_as_3052_, lean_object* v_i_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___redArg(v_givenName_3047_, v_skipAuxDecl_3048_, v_auxDeclToFullName_3049_, v___x_3050_, v_givenNameView_3051_, v_as_3052_, v_i_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15___boxed(lean_object* v_givenName_3056_, lean_object* v_skipAuxDecl_3057_, lean_object* v_auxDeclToFullName_3058_, lean_object* v___x_3059_, lean_object* v_givenNameView_3060_, lean_object* v_as_3061_, lean_object* v_i_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3064_; lean_object* v_res_3065_; 
v_skipAuxDecl_boxed_3064_ = lean_unbox(v_skipAuxDecl_3057_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__9_spec__12_spec__15(v_givenName_3056_, v_skipAuxDecl_boxed_3064_, v_auxDeclToFullName_3058_, v___x_3059_, v_givenNameView_3060_, v_as_3061_, v_i_3062_, v_a_3063_);
lean_dec_ref(v_as_3061_);
lean_dec(v_auxDeclToFullName_3058_);
lean_dec(v_givenName_3056_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(lean_object* v_localDecl_x3f_3066_, lean_object* v_givenName_3067_, lean_object* v_as_3068_, lean_object* v_i_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___redArg(v_localDecl_x3f_3066_, v_givenName_3067_, v_as_3068_, v_i_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19___boxed(lean_object* v_localDecl_x3f_3072_, lean_object* v_givenName_3073_, lean_object* v_as_3074_, lean_object* v_i_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__5_spec__10_spec__15_spec__19(v_localDecl_x3f_3072_, v_givenName_3073_, v_as_3074_, v_i_3075_, v_a_3076_);
lean_dec_ref(v_as_3074_);
lean_dec(v_givenName_3073_);
lean_dec(v_localDecl_x3f_3072_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(lean_object* v_opt_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___redArg(v_opt_3078_, v___y_3081_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30___boxed(lean_object* v_opt_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___at___00Lean_unresolveNameGlobal_x3f___at___00Lean_unresolveNameGlobalAvoidingLocals_x3f___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__2_spec__6_spec__16_spec__24_spec__28_spec__30(v_opt_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v_opt_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v_env_3096_; lean_object* v___x_3097_; lean_object* v_toEnvExtension_3098_; lean_object* v_asyncMode_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_merged_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
v___x_3095_ = lean_st_ref_get(v___y_3093_);
v_env_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc_ref(v_env_3096_);
lean_dec(v___x_3095_);
v___x_3097_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3098_ = lean_ctor_get(v___x_3097_, 0);
v_asyncMode_3099_ = lean_ctor_get(v_toEnvExtension_3098_, 2);
v___x_3100_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3101_ = lean_box(0);
v___x_3102_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3100_, v___x_3097_, v_env_3096_, v_asyncMode_3099_, v___x_3101_);
v_merged_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3102_, 1);
lean_dec(v_unused_3112_);
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_merged_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v_merged_3103_);
lean_ctor_set(v___x_3105_, 0, v_o_3092_);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_o_3092_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_merged_3103_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3113_, v___y_3114_);
lean_dec(v___y_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_options_3122_; lean_object* v___x_3123_; 
v_options_3122_ = lean_ctor_get(v___y_3119_, 2);
lean_inc_ref(v_options_3122_);
v___x_3123_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_3122_, v___y_3120_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3129_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_3132_ = l_Lean_stringToMessageData(v___x_3131_);
return v___x_3132_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_3150_ = l_Lean_stringToMessageData(v___x_3149_);
return v___x_3150_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_3153_ = l_Lean_stringToMessageData(v___x_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_3156_ = l_Lean_stringToMessageData(v___x_3155_);
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_3160_ = l_Lean_MessageData_ofFormat(v___x_3159_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_3163_ = l_Lean_stringToMessageData(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__29(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__28));
v___x_3175_ = l_Lean_stringToMessageData(v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__31(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__30));
v___x_3178_ = l_Lean_stringToMessageData(v___x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_3179_, uint8_t v_allowSuggestion_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3359_; 
v___x_3186_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3359_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3359_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v_extraMsg_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; 
v___x_3191_ = l_Lean_Linter_linter_deprecated;
v___x_3192_ = l_Lean_Linter_getLinterValue(v___x_3191_, v_a_3187_);
lean_dec(v_a_3187_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_dec(v_declName_3179_);
v___x_3208_ = lean_box(0);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3208_);
v___x_3210_ = v___x_3189_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
else
{
lean_object* v___x_3212_; lean_object* v_env_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3212_ = lean_st_ref_get(v_a_3184_);
v_env_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_ref(v_env_3213_);
lean_dec(v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_3215_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_3179_);
v___x_3216_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_3214_, v___x_3215_, v_env_3213_, v_declName_3179_);
if (lean_obj_tag(v___x_3216_) == 1)
{
lean_object* v_val_3217_; lean_object* v_text_x3f_3218_; 
lean_del_object(v___x_3189_);
v_val_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v_text_x3f_3218_ = lean_ctor_get(v_val_3217_, 1);
if (lean_obj_tag(v_text_x3f_3218_) == 0)
{
lean_object* v_newName_x3f_3219_; 
v_newName_x3f_3219_ = lean_ctor_get(v_val_3217_, 0);
lean_inc(v_newName_x3f_3219_);
lean_dec(v_val_3217_);
if (lean_obj_tag(v_newName_x3f_3219_) == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_3194_ = v___x_3220_;
v___y_3195_ = v_a_3181_;
v___y_3196_ = v_a_3182_;
v___y_3197_ = v_a_3183_;
v___y_3198_ = v_a_3184_;
goto v___jp_3193_;
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3222_; lean_object* v_env_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; 
v_val_3221_ = lean_ctor_get(v_newName_x3f_3219_, 0);
lean_inc_n(v_val_3221_, 2);
lean_dec_ref_known(v_newName_x3f_3219_, 1);
v___x_3222_ = lean_st_ref_get(v_a_3184_);
v_env_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc_ref_n(v_env_3223_, 2);
lean_dec(v___x_3222_);
v___x_3224_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_3225_ = l_Lean_MessageData_ofConstName(v_val_3221_, v___x_3192_);
lean_inc_ref(v___x_3225_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3226_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = l_Lean_Name_getPrefix(v_declName_3179_);
v___x_3230_ = 0;
lean_inc(v_declName_3179_);
v___x_3231_ = l_Lean_Environment_find_x3f(v_env_3223_, v_declName_3179_, v___x_3230_);
if (lean_obj_tag(v___x_3231_) == 1)
{
lean_object* v_val_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_val_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = l_Lean_Name_getPrefix(v_val_3221_);
lean_inc(v_val_3221_);
lean_inc_ref(v_env_3223_);
v___x_3234_ = l_Lean_Environment_find_x3f(v_env_3223_, v_val_3221_, v___x_3230_);
if (lean_obj_tag(v___x_3234_) == 1)
{
lean_object* v_val_3235_; lean_object* v___x_3236_; 
v_val_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_3232_, v_val_3235_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v_msg_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v_msg_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; uint8_t v___x_3331_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3331_ = lean_unbox(v_a_3237_);
if (v___x_3331_ == 0)
{
if (v___x_3192_ == 0)
{
lean_dec(v_val_3235_);
lean_dec(v_val_3232_);
v_msg_3324_ = v___x_3228_;
v___y_3325_ = v_a_3181_;
v___y_3326_ = v_a_3182_;
v___y_3327_ = v_a_3183_;
v___y_3328_ = v_a_3184_;
goto v___jp_3323_;
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3332_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_3333_ = l_Lean_ConstantInfo_type(v_val_3235_);
lean_dec(v_val_3235_);
v___x_3334_ = l_Lean_indentExpr(v___x_3333_);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3332_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_ConstantInfo_type(v_val_3232_);
lean_dec(v_val_3232_);
v___x_3339_ = l_Lean_indentExpr(v___x_3338_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3337_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = l_Lean_MessageData_note(v___x_3340_);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3228_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v_msg_3324_ = v___x_3342_;
v___y_3325_ = v_a_3181_;
v___y_3326_ = v_a_3182_;
v___y_3327_ = v_a_3183_;
v___y_3328_ = v_a_3184_;
goto v___jp_3323_;
}
}
else
{
lean_dec(v_val_3235_);
lean_dec(v_val_3232_);
v_msg_3324_ = v___x_3228_;
v___y_3325_ = v_a_3181_;
v___y_3326_ = v_a_3182_;
v___y_3327_ = v_a_3183_;
v___y_3328_ = v_a_3184_;
goto v___jp_3323_;
}
v___jp_3238_:
{
if (v_allowSuggestion_3180_ == 0)
{
lean_dec(v_a_3237_);
lean_dec(v_val_3221_);
v_extraMsg_3194_ = v_msg_3239_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3241_;
v___y_3197_ = v___y_3242_;
v___y_3198_ = v___y_3243_;
goto v___jp_3193_;
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3244_ == 0)
{
lean_dec(v_val_3221_);
v_extraMsg_3194_ = v_msg_3239_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3241_;
v___y_3197_ = v___y_3242_;
v___y_3198_ = v___y_3243_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3245_; 
lean_inc(v_declName_3179_);
v___x_3245_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f(v_declName_3179_, v_val_3221_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
if (lean_obj_tag(v_a_3246_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3248_; 
v_val_3247_ = lean_ctor_get(v_a_3246_, 0);
lean_inc(v_val_3247_);
lean_dec_ref_known(v_a_3246_, 1);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_msg_3239_);
lean_ctor_set(v___x_3248_, 1, v_val_3247_);
v_extraMsg_3194_ = v___x_3248_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3241_;
v___y_3197_ = v___y_3242_;
v___y_3198_ = v___y_3243_;
goto v___jp_3193_;
}
else
{
lean_dec(v_a_3246_);
v_extraMsg_3194_ = v_msg_3239_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3241_;
v___y_3197_ = v___y_3242_;
v___y_3198_ = v___y_3243_;
goto v___jp_3193_;
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v_msg_3239_);
lean_dec(v_declName_3179_);
v_a_3249_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3245_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3245_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
v___jp_3257_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3264_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3225_);
v___x_3266_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
lean_ctor_set(v___x_3268_, 1, v___y_3263_);
v___x_3269_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_MessageData_ofName(v___x_3233_);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_MessageData_note(v___x_3274_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___y_3261_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v_msg_3239_ = v___x_3276_;
v___y_3240_ = v___y_3260_;
v___y_3241_ = v___y_3259_;
v___y_3242_ = v___y_3258_;
v___y_3243_ = v___y_3262_;
goto v___jp_3238_;
}
v___jp_3277_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3284_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___y_3283_);
v___x_3286_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_MessageData_note(v___x_3287_);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___y_3281_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v_msg_3239_ = v___x_3289_;
v___y_3240_ = v___y_3280_;
v___y_3241_ = v___y_3279_;
v___y_3242_ = v___y_3278_;
v___y_3243_ = v___y_3282_;
goto v___jp_3238_;
}
v___jp_3290_:
{
if (v___y_3297_ == 0)
{
uint8_t v___x_3298_; 
lean_inc(v_declName_3179_);
lean_inc_ref(v_env_3223_);
v___x_3298_ = l_Lean_isProtected(v_env_3223_, v_declName_3179_);
if (v___x_3298_ == 0)
{
if (v___x_3192_ == 0)
{
lean_dec(v___x_3233_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
v_msg_3239_ = v___y_3295_;
v___y_3240_ = v___y_3294_;
v___y_3241_ = v___y_3292_;
v___y_3242_ = v___y_3291_;
v___y_3243_ = v___y_3296_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3299_; 
lean_inc(v_val_3221_);
v___x_3299_ = l_Lean_isProtected(v_env_3223_, v_val_3221_);
if (v___x_3299_ == 0)
{
lean_dec(v___x_3233_);
lean_dec_ref(v___x_3225_);
v_msg_3239_ = v___y_3295_;
v___y_3240_ = v___y_3294_;
v___y_3241_ = v___y_3292_;
v___y_3242_ = v___y_3291_;
v___y_3243_ = v___y_3296_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
lean_inc(v___x_3233_);
v___x_3300_ = l_Lean_Name_componentsRev(v___x_3233_);
v___x_3301_ = lean_unsigned_to_nat(1u);
v___x_3302_ = l_List_lengthTR___redArg(v___x_3300_);
v___x_3303_ = lean_nat_dec_lt(v___x_3301_, v___x_3302_);
lean_dec(v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; 
lean_dec(v___x_3300_);
v___x_3304_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___y_3258_ = v___y_3291_;
v___y_3259_ = v___y_3292_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3295_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___x_3304_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3305_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___x_3306_ = lean_unsigned_to_nat(0u);
v___x_3307_ = l_List_get___redArg(v___x_3300_, v___x_3306_);
lean_dec(v___x_3300_);
v___x_3308_ = l_Lean_MessageData_ofName(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3305_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___y_3258_ = v___y_3291_;
v___y_3259_ = v___y_3292_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3295_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___x_3311_;
goto v___jp_3257_;
}
}
}
}
else
{
lean_dec(v___x_3233_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
v_msg_3239_ = v___y_3295_;
v___y_3240_ = v___y_3294_;
v___y_3241_ = v___y_3292_;
v___y_3242_ = v___y_3291_;
v___y_3243_ = v___y_3296_;
goto v___jp_3238_;
}
}
else
{
lean_dec(v___x_3233_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
if (lean_obj_tag(v_declName_3179_) == 1)
{
lean_object* v_str_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_str_3312_ = lean_ctor_get(v_declName_3179_, 1);
v___x_3313_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
lean_inc_ref(v_str_3312_);
v___x_3314_ = l_Lean_stringToMessageData(v_str_3312_);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
lean_inc(v_val_3221_);
v___x_3318_ = l_Lean_MessageData_ofConstName(v_val_3221_, v___y_3293_);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__29, &l_Lean_Linter_checkDeprecated___closed__29_once, _init_l_Lean_Linter_checkDeprecated___closed__29);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___y_3278_ = v___y_3291_;
v___y_3279_ = v___y_3292_;
v___y_3280_ = v___y_3294_;
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3296_;
v___y_3283_ = v___x_3321_;
goto v___jp_3277_;
}
else
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_MessageData_nil;
v___y_3278_ = v___y_3291_;
v___y_3279_ = v___y_3292_;
v___y_3280_ = v___y_3294_;
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3296_;
v___y_3283_ = v___x_3322_;
goto v___jp_3277_;
}
}
}
v___jp_3323_:
{
uint8_t v___x_3329_; 
v___x_3329_ = l_Lean_Name_isAnonymous(v___x_3229_);
if (v___x_3329_ == 0)
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_name_eq(v___x_3229_, v___x_3233_);
lean_dec(v___x_3229_);
if (v___x_3330_ == 0)
{
v___y_3291_ = v___y_3327_;
v___y_3292_ = v___y_3326_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v___y_3325_;
v___y_3295_ = v_msg_3324_;
v___y_3296_ = v___y_3328_;
v___y_3297_ = v___x_3192_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v___y_3327_;
v___y_3292_ = v___y_3326_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v___y_3325_;
v___y_3295_ = v_msg_3324_;
v___y_3296_ = v___y_3328_;
v___y_3297_ = v___x_3329_;
goto v___jp_3290_;
}
}
else
{
lean_dec(v___x_3233_);
lean_dec(v___x_3229_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
v_msg_3239_ = v_msg_3324_;
v___y_3240_ = v___y_3325_;
v___y_3241_ = v___y_3326_;
v___y_3242_ = v___y_3327_;
v___y_3243_ = v___y_3328_;
goto v___jp_3238_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_val_3235_);
lean_dec(v___x_3233_);
lean_dec(v_val_3232_);
lean_dec(v___x_3229_);
lean_dec_ref_known(v___x_3228_, 2);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
lean_dec(v_val_3221_);
lean_dec(v_declName_3179_);
v_a_3343_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3236_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3236_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_dec(v___x_3234_);
lean_dec(v___x_3233_);
lean_dec(v_val_3232_);
lean_dec(v___x_3229_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
lean_dec(v_val_3221_);
v_extraMsg_3194_ = v___x_3228_;
v___y_3195_ = v_a_3181_;
v___y_3196_ = v_a_3182_;
v___y_3197_ = v_a_3183_;
v___y_3198_ = v_a_3184_;
goto v___jp_3193_;
}
}
else
{
lean_dec(v___x_3231_);
lean_dec(v___x_3229_);
lean_dec_ref(v___x_3225_);
lean_dec_ref(v_env_3223_);
lean_dec(v_val_3221_);
v_extraMsg_3194_ = v___x_3228_;
v___y_3195_ = v_a_3181_;
v___y_3196_ = v_a_3182_;
v___y_3197_ = v_a_3183_;
v___y_3198_ = v_a_3184_;
goto v___jp_3193_;
}
}
}
else
{
lean_object* v_val_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_inc_ref(v_text_x3f_3218_);
lean_dec(v_val_3217_);
v_val_3351_ = lean_ctor_get(v_text_x3f_3218_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v_text_x3f_3218_, 1);
v___x_3352_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__31, &l_Lean_Linter_checkDeprecated___closed__31_once, _init_l_Lean_Linter_checkDeprecated___closed__31);
v___x_3353_ = l_Lean_stringToMessageData(v_val_3351_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v_extraMsg_3194_ = v___x_3354_;
v___y_3195_ = v_a_3181_;
v___y_3196_ = v_a_3182_;
v___y_3197_ = v_a_3183_;
v___y_3198_ = v_a_3184_;
goto v___jp_3193_;
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
lean_dec(v___x_3216_);
lean_dec(v_declName_3179_);
v___x_3355_ = lean_box(0);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3355_);
v___x_3357_ = v___x_3189_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
v___jp_3193_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3199_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3300665414____hygCtx___hyg_2_));
v___x_3200_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_3201_ = l_Lean_MessageData_ofConstName(v_declName_3179_, v___x_3192_);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3200_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_3204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v_extraMsg_3194_);
v___x_3206_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3199_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_mkDeprecationHint_x3f_spec__0_spec__1_spec__3(v___x_3206_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_3360_, lean_object* v_allowSuggestion_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
uint8_t v_allowSuggestion_boxed_3367_; lean_object* v_res_3368_; 
v_allowSuggestion_boxed_3367_ = lean_unbox(v_allowSuggestion_3361_);
v_res_3368_ = l_Lean_Linter_checkDeprecated(v_declName_3360_, v_allowSuggestion_boxed_3367_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3369_, v___y_3373_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3382_;
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
