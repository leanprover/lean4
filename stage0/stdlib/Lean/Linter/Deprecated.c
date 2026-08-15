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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
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
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
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
size_t lean_usize_shift_right(size_t, size_t);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Try this: +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "`[deprecated]` attribute should specify either a new name or a deprecation message"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "The updated constant has a different type:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\ninstead of"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 374, .m_capacity = 374, .m_length = 373, .m_data = "\n\nThis suggests that addressing the deprecation might be more involved than simply replacing the old name with the new name. This is often excepected, but sometimes it indicates that the deprecation is in favor of the wrong declaration, or that there is a mistake in one of the statements.\n\nIf the type difference is intentional, use `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Add `+typeChanged` to silence this warning."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid `[deprecated]` attribute syntax"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add `+typeChanged`:"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " +typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "+typeChanged"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "The `+typeChanged` marker is not needed because the updated constant has the same type."};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__27_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Invalid `[deprecated]` attribute: `"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be deprecated in favor of itself"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecatedAttr"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 246, 23, 143, 159, 138, 155, 162)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 182, 79, 155, 204, 118, 39, 140)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark declaration as deprecated"};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "The updated constant is in a different namespace. Dot notation may need to be changed"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__4 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__5;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__6 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__7;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": Use `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__8 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__9;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__10 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__11;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` is protected. References to this constant must include "};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__12 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__13;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "its prefix `"};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__14 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__15;
static const lean_string_object l_Lean_Linter_checkDeprecated___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` even when inside its namespace."};
static const lean_object* l_Lean_Linter_checkDeprecated___closed__16 = (const lean_object*)&l_Lean_Linter_checkDeprecated___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkDeprecated___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkDeprecated___closed__17;
static const lean_ctor_object l_Lean_Linter_checkDeprecated___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4(lean_object* v_x_121_, lean_object* v_x_122_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(v_x_136_);
lean_dec_ref(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(v_x_145_, v_x_146_, v_x_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v_x_147_);
lean_dec_ref(v_x_146_);
lean_dec(v_x_145_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(uint8_t v___y_159_, uint8_t v_suppressElabErrors_160_, lean_object* v_x_161_){
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
v___x_166_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__0));
v___x_167_ = lean_string_dec_eq(v_str_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__1));
v___x_169_ = lean_string_dec_eq(v_str_165_, v___x_168_);
if (v___x_169_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__2));
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
v___x_172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__3));
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
v___x_178_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__4));
v___x_179_ = lean_string_dec_eq(v_str_177_, v___x_178_);
if (v___x_179_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__5));
v___x_181_ = lean_string_dec_eq(v_str_176_, v___x_180_);
if (v___x_181_ == 0)
{
return v___y_159_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__6));
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
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___closed__7));
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v___y_187_, lean_object* v_suppressElabErrors_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___y_15819__boxed_190_; uint8_t v_suppressElabErrors_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v___y_15819__boxed_190_ = lean_unbox(v___y_187_);
v_suppressElabErrors_boxed_191_ = lean_unbox(v_suppressElabErrors_188_);
v_res_192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0(v___y_15819__boxed_190_, v_suppressElabErrors_boxed_191_, v_x_189_);
lean_dec(v_x_189_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_ctor_set(v___x_199_, 2, v___x_198_);
lean_ctor_set(v___x_199_, 3, v___x_198_);
lean_ctor_set(v___x_199_, 4, v___x_197_);
lean_ctor_set(v___x_199_, 5, v___x_197_);
lean_ctor_set(v___x_199_, 6, v___x_197_);
lean_ctor_set(v___x_199_, 7, v___x_197_);
lean_ctor_set(v___x_199_, 8, v___x_197_);
lean_ctor_set(v___x_199_, 9, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_unsigned_to_nat(32u);
v___x_201_ = lean_mk_empty_array_with_capacity(v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = ((size_t)5ULL);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_unsigned_to_nat(32u);
v___x_206_ = lean_mk_empty_array_with_capacity(v___x_205_);
v___x_207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_208_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_204_);
lean_ctor_set(v___x_208_, 3, v___x_204_);
lean_ctor_set_usize(v___x_208_, 4, v___x_203_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_box(1);
v___x_210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v_env_218_; lean_object* v_options_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_217_ = lean_st_ref_get(v___y_215_);
v_env_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref(v_env_218_);
lean_dec(v___x_217_);
v_options_219_ = lean_ctor_get(v___y_214_, 2);
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_219_);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v_env_218_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_ctor_set(v___x_222_, 3, v_options_219_);
v___x_223_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_msgData_213_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(v_msgData_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_opts_230_, lean_object* v_opt_231_){
_start:
{
lean_object* v_name_232_; lean_object* v_defValue_233_; lean_object* v_map_234_; lean_object* v___x_235_; 
v_name_232_ = lean_ctor_get(v_opt_231_, 0);
v_defValue_233_ = lean_ctor_get(v_opt_231_, 1);
v_map_234_ = lean_ctor_get(v_opts_230_, 0);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_234_, v_name_232_);
if (lean_obj_tag(v___x_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = lean_unbox(v_defValue_233_);
return v___x_236_;
}
else
{
lean_object* v_val_237_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_val_237_) == 1)
{
uint8_t v_v_238_; 
v_v_238_ = lean_ctor_get_uint8(v_val_237_, 0);
lean_dec_ref_known(v_val_237_, 0);
return v_v_238_;
}
else
{
uint8_t v___x_239_; 
lean_dec(v_val_237_);
v___x_239_ = lean_unbox(v_defValue_233_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_240_, lean_object* v_opt_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_opts_240_, v_opt_241_);
lean_dec_ref(v_opt_241_);
lean_dec_ref(v_opts_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_ref_245_, lean_object* v_msgData_246_, uint8_t v_severity_247_, uint8_t v_isSilent_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_289_; uint8_t v___y_290_; uint8_t v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_314_; uint8_t v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_325_; uint8_t v___y_326_; uint8_t v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; uint8_t v___x_336_; uint8_t v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; uint8_t v___y_344_; uint8_t v___y_346_; uint8_t v___x_361_; 
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
lean_ctor_set(v___x_278_, 1, v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc_ref(v___y_259_);
v___x_279_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_279_, 0, v___y_259_);
lean_ctor_set(v___x_279_, 1, v___y_254_);
lean_ctor_set(v___x_279_, 2, v___y_255_);
lean_ctor_set(v___x_279_, 3, v___y_257_);
lean_ctor_set(v___x_279_, 4, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*5, v___y_256_);
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
v___x_283_ = lean_st_ref_set(v___y_261_, v___x_282_);
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
v___x_298_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(v___x_297_, v___y_249_, v___y_250_);
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
lean_inc_ref_n(v___y_294_, 2);
v___x_303_ = l_Lean_FileMap_toPosition(v___y_294_, v___y_293_);
lean_dec(v___y_293_);
v___x_304_ = l_Lean_FileMap_toPosition(v___y_294_, v___y_296_);
lean_dec(v___y_296_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_290_ == 0)
{
lean_del_object(v___x_301_);
lean_dec_ref(v___y_289_);
v___y_253_ = v___y_291_;
v___y_254_ = v___x_303_;
v___y_255_ = v___x_305_;
v___y_256_ = v___y_292_;
v___y_257_ = v___x_306_;
v___y_258_ = v_a_299_;
v___y_259_ = v___y_295_;
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
v___y_253_ = v___y_291_;
v___y_254_ = v___x_303_;
v___y_255_ = v___x_305_;
v___y_256_ = v___y_292_;
v___y_257_ = v___x_306_;
v___y_258_ = v_a_299_;
v___y_259_ = v___y_295_;
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
v___x_322_ = l_Lean_Syntax_getTailPos_x3f(v___y_317_, v___y_319_);
lean_dec(v___y_317_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_inc(v___y_321_);
v___y_289_ = v___y_314_;
v___y_290_ = v___y_316_;
v___y_291_ = v___y_315_;
v___y_292_ = v___y_319_;
v___y_293_ = v___y_321_;
v___y_294_ = v___y_318_;
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
v___y_290_ = v___y_316_;
v___y_291_ = v___y_315_;
v___y_292_ = v___y_319_;
v___y_293_ = v___y_321_;
v___y_294_ = v___y_318_;
v___y_295_ = v___y_320_;
v___y_296_ = v_val_323_;
goto v___jp_288_;
}
}
v___jp_324_:
{
lean_object* v_ref_332_; lean_object* v___x_333_; 
v_ref_332_ = l_Lean_replaceRef(v_ref_245_, v___y_329_);
v___x_333_ = l_Lean_Syntax_getPos_x3f(v_ref_332_, v___y_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___y_314_ = v___y_325_;
v___y_315_ = v___y_331_;
v___y_316_ = v___y_326_;
v___y_317_ = v_ref_332_;
v___y_318_ = v___y_328_;
v___y_319_ = v___y_327_;
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
v___y_317_ = v_ref_332_;
v___y_318_ = v___y_328_;
v___y_319_ = v___y_327_;
v___y_320_ = v___y_330_;
v___y_321_ = v_val_335_;
goto v___jp_313_;
}
}
v___jp_337_:
{
if (v___y_344_ == 0)
{
v___y_325_ = v___y_339_;
v___y_326_ = v___y_338_;
v___y_327_ = v___y_343_;
v___y_328_ = v___y_340_;
v___y_329_ = v___y_341_;
v___y_330_ = v___y_342_;
v___y_331_ = v_severity_247_;
goto v___jp_324_;
}
else
{
v___y_325_ = v___y_339_;
v___y_326_ = v___y_338_;
v___y_327_ = v___y_343_;
v___y_328_ = v___y_340_;
v___y_329_ = v___y_341_;
v___y_330_ = v___y_342_;
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
v___f_354_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_354_, 0, v___x_352_);
lean_closure_set(v___f_354_, 1, v___x_353_);
v___x_355_ = 1;
v___x_356_ = l_Lean_instBEqMessageSeverity_beq(v_severity_247_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_338_ = v_suppressElabErrors_351_;
v___y_339_ = v___f_354_;
v___y_340_ = v_fileMap_348_;
v___y_341_ = v_ref_350_;
v___y_342_ = v_fileName_347_;
v___y_343_ = v___y_346_;
v___y_344_ = v___x_356_;
goto v___jp_337_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = l_Lean_warningAsError;
v___x_358_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_349_, v___x_357_);
v___y_338_ = v_suppressElabErrors_351_;
v___y_339_ = v___f_354_;
v___y_340_ = v_fileMap_348_;
v___y_341_ = v_ref_350_;
v___y_342_ = v_fileName_347_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_ref_363_, lean_object* v_msgData_364_, lean_object* v_severity_365_, lean_object* v_isSilent_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_severity_boxed_370_; uint8_t v_isSilent_boxed_371_; lean_object* v_res_372_; 
v_severity_boxed_370_ = lean_unbox(v_severity_365_);
v_isSilent_boxed_371_ = lean_unbox(v_isSilent_366_);
v_res_372_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_363_, v_msgData_364_, v_severity_boxed_370_, v_isSilent_boxed_371_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_ref_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_373_, uint8_t v_severity_374_, uint8_t v_isSilent_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_ref_379_; lean_object* v___x_380_; 
v_ref_379_ = lean_ctor_get(v___y_376_, 5);
v___x_380_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_ref_379_, v_msgData_373_, v_severity_374_, v_isSilent_375_, v___y_376_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_381_, lean_object* v_severity_382_, lean_object* v_isSilent_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_severity_boxed_387_; uint8_t v_isSilent_boxed_388_; lean_object* v_res_389_; 
v_severity_boxed_387_ = lean_unbox(v_severity_382_);
v_isSilent_boxed_388_ = lean_unbox(v_isSilent_383_);
v_res_389_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2(v_msgData_381_, v_severity_boxed_387_, v_isSilent_boxed_388_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(lean_object* v_msgData_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = 1;
v___x_395_ = 0;
v___x_396_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2(v_msgData_390_, v___x_394_, v___x_395_, v___y_391_, v___y_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1___boxed(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(v_msgData_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg(lean_object* v_o_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_env_406_; lean_object* v___x_407_; lean_object* v_toEnvExtension_408_; lean_object* v_asyncMode_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_merged_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v___x_407_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_408_ = lean_ctor_get(v___x_407_, 0);
v_asyncMode_409_ = lean_ctor_get(v_toEnvExtension_408_, 2);
v___x_410_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_411_ = lean_box(0);
v___x_412_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_410_, v___x_407_, v_env_406_, v_asyncMode_409_, v___x_411_);
v_merged_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_412_, 1);
lean_dec(v_unused_422_);
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_merged_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_merged_413_);
lean_ctor_set(v___x_415_, 0, v_o_402_);
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_o_402_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_merged_413_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(lean_object* v_o_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_423_, v___y_424_);
lean_dec(v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3(lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_options_430_; lean_object* v___x_431_; 
v_options_430_ = lean_ctor_get(v___y_427_, 2);
lean_inc_ref(v_options_430_);
v___x_431_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg(v_options_430_, v___y_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3(v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_ref_440_; lean_object* v___x_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_ref_440_ = lean_ctor_get(v___y_437_, 5);
v___x_441_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(v_msg_436_, v___y_437_, v___y_438_);
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_inc(v_ref_440_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_ref_440_);
lean_ctor_set(v___x_446_, 1, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v_msg_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(lean_object* v_a_456_, lean_object* v_x_457_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg___boxed(lean_object* v_a_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_465_, v_x_466_);
lean_dec(v_x_466_);
lean_dec(v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg(lean_object* v_m_468_, lean_object* v_a_469_){
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
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_469_, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_m_489_);
return v_res_491_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_492_; double v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_float_of_nat(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8(lean_object* v_cls_496_, lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_ref_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_547_; 
v_ref_501_ = lean_ctor_get(v___y_498_, 5);
v___x_502_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0(v_msg_497_, v___y_498_, v___y_499_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_547_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_547_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_547_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v_traceState_508_; lean_object* v_env_509_; lean_object* v_nextMacroScope_510_; lean_object* v_ngen_511_; lean_object* v_auxDeclNGen_512_; lean_object* v_cache_513_; lean_object* v_messages_514_; lean_object* v_infoState_515_; lean_object* v_snapshotTasks_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_546_; 
v___x_507_ = lean_st_ref_take(v___y_499_);
v_traceState_508_ = lean_ctor_get(v___x_507_, 4);
v_env_509_ = lean_ctor_get(v___x_507_, 0);
v_nextMacroScope_510_ = lean_ctor_get(v___x_507_, 1);
v_ngen_511_ = lean_ctor_get(v___x_507_, 2);
v_auxDeclNGen_512_ = lean_ctor_get(v___x_507_, 3);
v_cache_513_ = lean_ctor_get(v___x_507_, 5);
v_messages_514_ = lean_ctor_get(v___x_507_, 6);
v_infoState_515_ = lean_ctor_get(v___x_507_, 7);
v_snapshotTasks_516_ = lean_ctor_get(v___x_507_, 8);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_546_ == 0)
{
v___x_518_ = v___x_507_;
v_isShared_519_ = v_isSharedCheck_546_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snapshotTasks_516_);
lean_inc(v_infoState_515_);
lean_inc(v_messages_514_);
lean_inc(v_cache_513_);
lean_inc(v_traceState_508_);
lean_inc(v_auxDeclNGen_512_);
lean_inc(v_ngen_511_);
lean_inc(v_nextMacroScope_510_);
lean_inc(v_env_509_);
lean_dec(v___x_507_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_546_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint64_t v_tid_520_; lean_object* v_traces_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_545_; 
v_tid_520_ = lean_ctor_get_uint64(v_traceState_508_, sizeof(void*)*1);
v_traces_521_ = lean_ctor_get(v_traceState_508_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_traceState_508_);
if (v_isSharedCheck_545_ == 0)
{
v___x_523_ = v_traceState_508_;
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_traces_521_);
lean_dec(v_traceState_508_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; double v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__0);
v___x_527_ = 0;
v___x_528_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_529_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_529_, 0, v_cls_496_);
lean_ctor_set(v___x_529_, 1, v___x_525_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
lean_ctor_set_float(v___x_529_, sizeof(void*)*3, v___x_526_);
lean_ctor_set_float(v___x_529_, sizeof(void*)*3 + 8, v___x_526_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*3 + 16, v___x_527_);
v___x_530_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___closed__1));
v___x_531_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v_a_503_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
lean_inc(v_ref_501_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_ref_501_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_PersistentArray_push___redArg(v_traces_521_, v___x_532_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_533_);
v___x_535_ = v___x_523_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_533_);
lean_ctor_set_uint64(v_reuseFailAlloc_544_, sizeof(void*)*1, v_tid_520_);
v___x_535_ = v_reuseFailAlloc_544_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 4, v___x_535_);
v___x_537_ = v___x_518_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_env_509_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_nextMacroScope_510_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_ngen_511_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_auxDeclNGen_512_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_543_, 5, v_cache_513_);
lean_ctor_set(v_reuseFailAlloc_543_, 6, v_messages_514_);
lean_ctor_set(v_reuseFailAlloc_543_, 7, v_infoState_515_);
lean_ctor_set(v_reuseFailAlloc_543_, 8, v_snapshotTasks_516_);
v___x_537_ = v_reuseFailAlloc_543_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_st_ref_set(v___y_499_, v___x_537_);
v___x_539_ = lean_box(0);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_539_);
v___x_541_ = v___x_505_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8___boxed(lean_object* v_cls_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_548_, v_msg_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_553_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(lean_object* v_keys_554_, lean_object* v_i_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_keys_554_);
v___x_558_ = lean_nat_dec_lt(v_i_555_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_i_555_);
return v___x_558_;
}
else
{
lean_object* v_k_x27_559_; uint8_t v___x_560_; 
v_k_x27_559_ = lean_array_fget_borrowed(v_keys_554_, v_i_555_);
v___x_560_ = l_Lean_instBEqExtraModUse_beq(v_k_556_, v_k_x27_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_add(v_i_555_, v___x_561_);
lean_dec(v_i_555_);
v_i_555_ = v___x_562_;
goto _start;
}
else
{
lean_dec(v_i_555_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_keys_564_, lean_object* v_i_565_, lean_object* v_k_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_564_, v_i_565_, v_k_566_);
lean_dec_ref(v_k_566_);
lean_dec_ref(v_keys_564_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(lean_object* v_x_569_, size_t v_x_570_, lean_object* v_x_571_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v_es_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v_j_576_; lean_object* v___x_577_; 
v_es_572_ = lean_ctor_get(v_x_569_, 0);
v___x_573_ = lean_box(2);
v___x_574_ = ((size_t)31ULL);
v___x_575_ = lean_usize_land(v_x_570_, v___x_574_);
v_j_576_ = lean_usize_to_nat(v___x_575_);
v___x_577_ = lean_array_get_borrowed(v___x_573_, v_es_572_, v_j_576_);
lean_dec(v_j_576_);
switch(lean_obj_tag(v___x_577_))
{
case 0:
{
lean_object* v_key_578_; uint8_t v___x_579_; 
v_key_578_ = lean_ctor_get(v___x_577_, 0);
v___x_579_ = l_Lean_instBEqExtraModUse_beq(v_x_571_, v_key_578_);
return v___x_579_;
}
case 1:
{
lean_object* v_node_580_; size_t v___x_581_; size_t v___x_582_; 
v_node_580_ = lean_ctor_get(v___x_577_, 0);
v___x_581_ = ((size_t)5ULL);
v___x_582_ = lean_usize_shift_right(v_x_570_, v___x_581_);
v_x_569_ = v_node_580_;
v_x_570_ = v___x_582_;
goto _start;
}
default: 
{
uint8_t v___x_584_; 
v___x_584_ = 0;
return v___x_584_;
}
}
}
else
{
lean_object* v_ks_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_ks_585_ = lean_ctor_get(v_x_569_, 0);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_ks_585_, v___x_586_, v_x_571_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
size_t v_x_16457__boxed_591_; uint8_t v_res_592_; lean_object* v_r_593_; 
v_x_16457__boxed_591_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_res_592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_588_, v_x_16457__boxed_591_, v_x_590_);
lean_dec_ref(v_x_590_);
lean_dec_ref(v_x_588_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint64_t v___x_596_; size_t v___x_597_; uint8_t v___x_598_; 
v___x_596_ = l_Lean_instHashableExtraModUse_hash(v_x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_594_, v___x_597_, v_x_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_599_, v_x_600_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_x_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__1));
v___x_606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__0));
v___x_607_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_608_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__3);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__4);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__8));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__10));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_cls_626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_627_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__13));
v___x_628_ = l_Lean_Name_append(v___x_627_, v_cls_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__15));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__17));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_mod_639_, uint8_t v_isMeta_640_, lean_object* v_hint_641_, lean_object* v___y_642_, lean_object* v___y_643_){
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
v___x_650_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__2);
lean_inc(v_mod_639_);
v_entry_651_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_651_, 0, v_mod_639_);
lean_ctor_set_uint8(v_entry_651_, sizeof(void*)*1, v_isExporting_647_);
lean_ctor_set_uint8(v_entry_651_, sizeof(void*)*1 + 1, v_isMeta_640_);
v___x_652_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_653_ = lean_box(1);
v___x_654_ = lean_box(0);
v___x_681_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_650_, v___x_652_, v_env_649_, v___x_653_, v___x_654_);
v___x_682_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v___x_681_, v_entry_651_);
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
v_cls_686_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__7));
v___x_706_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__14);
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
v___x_708_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__16);
if (v_isExporting_647_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__21));
v___y_710_ = v___x_717_;
goto v___jp_709_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__22));
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
v___x_713_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__18);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
if (v_isMeta_640_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__19));
v___y_693_ = v___x_714_;
v___y_694_ = v___x_715_;
goto v___jp_692_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__20));
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
v___x_691_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__8(v_cls_686_, v___x_690_, v___y_642_, v___y_643_);
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
v___x_697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__9);
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
v___x_702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__11);
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
v___x_705_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12);
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
v___x_672_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__5);
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
v___x_675_ = lean_st_ref_set(v___y_656_, v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_mod_721_, lean_object* v_isMeta_722_, lean_object* v_hint_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_isMeta_boxed_727_; lean_object* v_res_728_; 
v_isMeta_boxed_727_ = lean_unbox(v_isMeta_722_);
v_res_728_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4(v_mod_721_, v_isMeta_boxed_727_, v_hint_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5(lean_object* v___x_729_, lean_object* v_declName_730_, lean_object* v_as_731_, size_t v_sz_732_, size_t v_i_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_){
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
v___x_748_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4(v_module_746_, v___x_747_, v_declName_730_, v___y_735_, v___y_736_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v___x_753_, lean_object* v_declName_754_, lean_object* v_as_755_, lean_object* v_sz_756_, lean_object* v_i_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_756_);
lean_dec(v_sz_756_);
v_i_boxed_763_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5(v___x_753_, v_declName_754_, v_as_755_, v_sz_boxed_762_, v_i_boxed_763_, v_b_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec_ref(v_as_755_);
lean_dec_ref(v___x_753_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__1));
v___x_768_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__0));
v___x_769_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_768_, v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2(lean_object* v_declName_772_, uint8_t v_isMeta_773_, lean_object* v___y_774_, lean_object* v___y_775_){
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
v___x_804_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__2);
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
v___x_810_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4(v_module_809_, v___y_807_, v_declName_772_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = l_Lean_indirectModUseExt;
v___x_812_ = lean_box(1);
v___x_813_ = lean_box(0);
lean_inc_ref(v_env_781_);
v___x_814_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_804_, v___x_811_, v_env_781_, v___x_812_, v___x_813_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_814_, v_declName_772_);
lean_dec(v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___closed__3));
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
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__5(v_env_781_, v_declName_772_, v___y_783_, v_sz_785_, v___x_786_, v___x_784_, v___y_774_, v___y_775_);
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
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2___boxed(lean_object* v_declName_820_, lean_object* v_isMeta_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
uint8_t v_isMeta_boxed_825_; lean_object* v_res_826_; 
v_isMeta_boxed_825_ = lean_unbox(v_isMeta_821_);
v_res_826_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2(v_declName_820_, v_isMeta_boxed_825_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_826_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_831_ = l_Lean_MessageData_ofFormat(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_836_ = l_Lean_MessageData_ofFormat(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_850_ = l_Lean_MessageData_ofFormat(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_852_ = l_Lean_MessageData_hint_x27(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_860_ = l_Lean_MessageData_ofFormat(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_868_ = l_Lean_MessageData_ofFormat(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__25_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__28_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_875_ = l_Lean_MessageData_ofFormat(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__30_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_box(1);
v___x_880_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_881_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
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
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__31_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
lean_ctor_set(v___x_891_, 4, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__36_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_893_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_894_ = lean_box(1);
v___x_895_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__35_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_896_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__34_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
lean_ctor_set(v___x_897_, 3, v___x_893_);
lean_ctor_set(v___x_897_, 4, v___x_892_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__38_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__40_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v_declName_907_, lean_object* v_stx_908_, lean_object* v___y_909_, lean_object* v___y_910_){
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
v___x_1028_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1029_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1028_, v___y_909_, v___y_910_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; lean_object* v_val_1042_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v_a_1091_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v_a_1168_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v_since_x3f_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v_typeChanged_x3f_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1224_; lean_object* v_text_x3f_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v_id_x3f_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
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
v___x_1253_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1254_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1253_, v___y_909_, v___y_910_);
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
v___x_1043_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__26_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
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
v___x_1056_ = l_Lean_MessageData_hint(v___x_1043_, v___x_1055_, v___x_1045_, v___x_1045_, v___y_1040_, v___y_1039_, v___y_1034_);
lean_dec_ref(v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_988_ = v___y_1033_;
v___y_989_ = v___y_1035_;
v___y_990_ = v___y_1036_;
v___y_991_ = v___y_1037_;
v___y_992_ = v___y_1038_;
v___y_993_ = v___y_1041_;
v_hint_994_ = v_a_1057_;
v___y_995_ = v___y_1039_;
v___y_996_ = v___y_1034_;
goto v___jp_987_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1033_);
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
if (lean_obj_tag(v___y_1075_) == 0)
{
lean_dec_ref(v___f_906_);
v___y_1019_ = v___y_1068_;
v___y_1020_ = v___y_1067_;
v___y_1021_ = v___y_1069_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1071_;
v___y_1024_ = v___y_1073_;
v___y_1025_ = v___y_1072_;
v___y_1026_ = v___y_1075_;
goto v___jp_1018_;
}
else
{
lean_object* v_val_1076_; lean_object* v___x_1077_; 
v_val_1076_ = lean_ctor_get(v___y_1075_, 0);
v___x_1077_ = l_Lean_Syntax_getTailPos_x3f(v_val_1076_, v___x_919_);
if (lean_obj_tag(v___x_1077_) == 1)
{
lean_object* v_val_1078_; 
v_val_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___y_1033_ = v___y_1068_;
v___y_1034_ = v___y_1067_;
v___y_1035_ = v___y_1069_;
v___y_1036_ = v___y_1070_;
v___y_1037_ = v___y_1071_;
v___y_1038_ = v___y_1073_;
v___y_1039_ = v___y_1072_;
v___y_1040_ = v___y_1074_;
v___y_1041_ = v___y_1075_;
v_val_1042_ = v_val_1078_;
goto v___jp_1032_;
}
else
{
lean_dec(v___x_1077_);
lean_dec_ref(v___f_906_);
v___y_1019_ = v___y_1068_;
v___y_1020_ = v___y_1067_;
v___y_1021_ = v___y_1069_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1071_;
v___y_1024_ = v___y_1073_;
v___y_1025_ = v___y_1072_;
v___y_1026_ = v___y_1075_;
goto v___jp_1018_;
}
}
}
v___jp_1079_:
{
if (v_a_1091_ == 0)
{
if (lean_obj_tag(v___y_1090_) == 0)
{
if (v___y_1084_ == 0)
{
lean_dec_ref(v___y_1087_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1081_;
v___y_972_ = v___y_1082_;
v___y_973_ = v___y_1083_;
v___y_974_ = v___y_1089_;
v___y_975_ = v___y_1086_;
v___y_976_ = v___y_1080_;
goto v___jp_970_;
}
else
{
if (lean_obj_tag(v___y_1082_) == 0)
{
v___y_1067_ = v___y_1080_;
v___y_1068_ = v___y_1081_;
v___y_1069_ = v___y_1082_;
v___y_1070_ = v___y_1083_;
v___y_1071_ = v___y_1085_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v___y_1087_;
v___y_1074_ = v___y_1088_;
v___y_1075_ = v___y_1089_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1093_; 
v_val_1092_ = lean_ctor_get(v___y_1082_, 0);
v___x_1093_ = l_Lean_Syntax_getTailPos_x3f(v_val_1092_, v___x_919_);
if (lean_obj_tag(v___x_1093_) == 0)
{
v___y_1067_ = v___y_1080_;
v___y_1068_ = v___y_1081_;
v___y_1069_ = v___y_1082_;
v___y_1070_ = v___y_1083_;
v___y_1071_ = v___y_1085_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v___y_1087_;
v___y_1074_ = v___y_1088_;
v___y_1075_ = v___y_1089_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1094_; 
v_val_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___y_1033_ = v___y_1081_;
v___y_1034_ = v___y_1080_;
v___y_1035_ = v___y_1082_;
v___y_1036_ = v___y_1083_;
v___y_1037_ = v___y_1085_;
v___y_1038_ = v___y_1087_;
v___y_1039_ = v___y_1086_;
v___y_1040_ = v___y_1088_;
v___y_1041_ = v___y_1089_;
v_val_1042_ = v_val_1094_;
goto v___jp_1032_;
}
}
}
}
else
{
lean_dec_ref_known(v___y_1090_, 1);
lean_dec_ref(v___y_1087_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1081_;
v___y_972_ = v___y_1082_;
v___y_973_ = v___y_1083_;
v___y_974_ = v___y_1089_;
v___y_975_ = v___y_1086_;
v___y_976_ = v___y_1080_;
goto v___jp_970_;
}
}
else
{
lean_dec_ref(v___y_1087_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___f_906_);
if (lean_obj_tag(v___y_1090_) == 0)
{
v___y_971_ = v___y_1081_;
v___y_972_ = v___y_1082_;
v___y_973_ = v___y_1083_;
v___y_974_ = v___y_1089_;
v___y_975_ = v___y_1086_;
v___y_976_ = v___y_1080_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref_known(v___y_1090_, 1);
v___x_1095_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__29_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1096_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(v___x_1095_, v___y_1086_, v___y_1080_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref_known(v___x_1096_, 1);
v___y_971_ = v___y_1081_;
v___y_972_ = v___y_1082_;
v___y_973_ = v___y_1083_;
v___y_974_ = v___y_1089_;
v___y_975_ = v___y_1086_;
v___y_976_ = v___y_1080_;
goto v___jp_970_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v___y_1089_);
lean_dec(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
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
if (lean_obj_tag(v___y_1108_) == 1)
{
lean_object* v_val_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
v_val_1113_ = lean_ctor_get(v___y_1108_, 0);
v___x_1114_ = 0;
lean_inc(v_val_1113_);
v___x_1115_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2(v_val_1113_, v___x_1114_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
lean_dec_ref_known(v___x_1115_, 1);
v___x_1116_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3(v___y_1111_, v___y_1112_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = l_Lean_Linter_linter_deprecated;
v___x_1119_ = l_Lean_Linter_getLinterValue(v___x_1118_, v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1119_ == 0)
{
lean_dec(v___y_1110_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1106_;
v___y_972_ = v___y_1107_;
v___y_973_ = v___y_1108_;
v___y_974_ = v___y_1109_;
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
v___x_1133_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__32_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1134_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__33_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
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
v___x_1137_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__37_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
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
v___y_1080_ = v___y_1112_;
v___y_1081_ = v___y_1106_;
v___y_1082_ = v___y_1107_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v___x_1119_;
v___y_1085_ = v_val_1123_;
v___y_1086_ = v___y_1111_;
v___y_1087_ = v_val_1125_;
v___y_1088_ = v___x_1114_;
v___y_1089_ = v___y_1109_;
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
v___y_1080_ = v___y_1112_;
v___y_1081_ = v___y_1106_;
v___y_1082_ = v___y_1107_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v___x_1119_;
v___y_1085_ = v_val_1123_;
v___y_1086_ = v___y_1111_;
v___y_1087_ = v_val_1125_;
v___y_1088_ = v___x_1114_;
v___y_1089_ = v___y_1109_;
v___y_1090_ = v___y_1110_;
v_a_1091_ = v___x_1144_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_val_1125_);
lean_dec(v_val_1123_);
lean_dec_ref_known(v___y_1108_, 1);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
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
lean_dec(v___y_1110_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1106_;
v___y_972_ = v___y_1107_;
v___y_973_ = v___y_1108_;
v___y_974_ = v___y_1109_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
}
else
{
lean_dec(v___x_1122_);
lean_dec_ref(v_env_1121_);
lean_dec(v___y_1110_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1106_;
v___y_972_ = v___y_1107_;
v___y_973_ = v___y_1108_;
v___y_974_ = v___y_1109_;
v___y_975_ = v___y_1111_;
v___y_976_ = v___y_1112_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref_known(v___y_1108_, 1);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
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
lean_dec(v___y_1110_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___y_971_ = v___y_1106_;
v___y_972_ = v___y_1107_;
v___y_973_ = v___y_1108_;
v___y_974_ = v___y_1109_;
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
v___x_1170_ = l_Option_instBEq_beq___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__4(v_a_1168_, v___x_1169_);
lean_dec_ref_known(v___x_1169_, 1);
if (v___x_1170_ == 0)
{
v___y_1106_ = v___y_1162_;
v___y_1107_ = v___y_1163_;
v___y_1108_ = v_a_1168_;
v___y_1109_ = v___y_1165_;
v___y_1110_ = v___y_1166_;
v___y_1111_ = v___y_1164_;
v___y_1112_ = v___y_1167_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1168_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___f_906_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__39_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1172_ = l_Lean_MessageData_ofConstName(v_declName_907_, v___x_919_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__41_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1175_, v___y_1164_, v___y_1167_);
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
if (lean_obj_tag(v___y_1187_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_box(0);
v___y_1162_ = v_since_x3f_1189_;
v___y_1163_ = v___y_1186_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1187_;
v___y_1166_ = v___y_1188_;
v___y_1167_ = v___y_1191_;
v_a_1168_ = v___x_1192_;
goto v___jp_1161_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_val_1193_ = lean_ctor_get(v___y_1187_, 0);
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
v___y_1162_ = v_since_x3f_1189_;
v___y_1163_ = v___y_1186_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1187_;
v___y_1166_ = v___y_1188_;
v___y_1167_ = v___y_1191_;
v_a_1168_ = v___x_1197_;
goto v___jp_1161_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref_known(v___y_1187_, 1);
lean_dec(v_since_x3f_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1186_);
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
lean_dec(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec(v_declName_907_);
lean_dec_ref(v___f_906_);
v___x_1218_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1218_, v___y_1211_, v___y_1212_);
return v___x_1219_;
}
else
{
lean_object* v_since_x3f_1220_; lean_object* v___x_1221_; 
v_since_x3f_1220_ = l_Lean_Syntax_getArg(v___x_1214_, v___y_1207_);
lean_dec(v___x_1214_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_since_x3f_1220_);
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v_typeChanged_x3f_1210_;
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
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v_typeChanged_x3f_1210_;
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
v___x_1232_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1233_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1232_, v___y_1226_, v___y_1227_);
return v___x_1233_;
}
else
{
lean_object* v_typeChanged_x3f_1234_; lean_object* v___x_1235_; 
v_typeChanged_x3f_1234_ = l_Lean_Syntax_getArg(v___x_1229_, v___x_1030_);
lean_dec(v___x_1229_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_typeChanged_x3f_1234_);
v___y_1207_ = v___x_1228_;
v___y_1208_ = v_text_x3f_1225_;
v___y_1209_ = v___y_1224_;
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
v___y_1207_ = v___x_1228_;
v___y_1208_ = v_text_x3f_1225_;
v___y_1209_ = v___y_1224_;
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
v___x_1245_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1246_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v___x_1245_, v___y_1239_, v___y_1240_);
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
lean_ctor_set(v___x_916_, 0, v___y_914_);
lean_ctor_set(v___x_916_, 1, v___y_913_);
lean_ctor_set(v___x_916_, 2, v___y_915_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
v___jp_920_:
{
if (lean_obj_tag(v___y_923_) == 0)
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
v___x_926_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_927_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(v___x_926_, v___y_924_, v___y_925_);
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
lean_dec(v___y_922_);
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
if (lean_obj_tag(v___y_941_) == 0)
{
if (v___x_919_ == 0)
{
v___y_921_ = v___y_937_;
v___y_922_ = v___y_938_;
v___y_923_ = v___y_942_;
v___y_924_ = v___y_939_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
else
{
if (lean_obj_tag(v___y_937_) == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_944_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(v___x_943_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref_known(v___x_944_, 1);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_938_;
v___y_923_ = v___y_942_;
v___y_924_ = v___y_939_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v___y_942_);
lean_dec(v___y_938_);
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
v___y_922_ = v___y_938_;
v___y_923_ = v___y_942_;
v___y_924_ = v___y_939_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
}
}
else
{
lean_dec_ref_known(v___y_941_, 1);
v___y_921_ = v___y_937_;
v___y_922_ = v___y_938_;
v___y_923_ = v___y_942_;
v___y_924_ = v___y_939_;
v___y_925_ = v___y_940_;
goto v___jp_920_;
}
}
v___jp_953_:
{
if (lean_obj_tag(v___y_954_) == 0)
{
lean_object* v___x_960_; 
v___x_960_ = lean_box(0);
v___y_937_ = v___y_959_;
v___y_938_ = v___y_955_;
v___y_939_ = v___y_956_;
v___y_940_ = v___y_957_;
v___y_941_ = v___y_958_;
v___y_942_ = v___x_960_;
goto v___jp_936_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_val_961_ = lean_ctor_get(v___y_954_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___y_954_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___y_954_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___y_954_);
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
v___y_938_ = v___y_955_;
v___y_939_ = v___y_956_;
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
if (lean_obj_tag(v___y_972_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_box(0);
v___y_954_ = v___y_971_;
v___y_955_ = v___y_973_;
v___y_956_ = v___y_975_;
v___y_957_ = v___y_976_;
v___y_958_ = v___y_974_;
v___y_959_ = v___x_977_;
goto v___jp_953_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_val_978_ = lean_ctor_get(v___y_972_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___y_972_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___y_972_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_val_978_);
lean_dec(v___y_972_);
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
v___y_954_ = v___y_971_;
v___y_955_ = v___y_973_;
v___y_956_ = v___y_975_;
v___y_957_ = v___y_976_;
v___y_958_ = v___y_974_;
v___y_959_ = v___x_984_;
goto v___jp_953_;
}
}
}
}
v___jp_987_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_997_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_998_ = l_Lean_ConstantInfo_type(v___y_992_);
lean_dec_ref(v___y_992_);
v___x_999_ = l_Lean_indentExpr(v___x_998_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_ConstantInfo_type(v___y_991_);
lean_dec_ref(v___y_991_);
v___x_1004_ = l_Lean_indentExpr(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_hint_994_);
v___x_1009_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1(v___x_1008_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec_ref_known(v___x_1009_, 1);
v___y_971_ = v___y_988_;
v___y_972_ = v___y_989_;
v___y_973_ = v___y_990_;
v___y_974_ = v___y_993_;
v___y_975_ = v___y_995_;
v___y_976_ = v___y_996_;
goto v___jp_970_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___y_993_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
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
v___x_1027_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___y_988_ = v___y_1019_;
v___y_989_ = v___y_1021_;
v___y_990_ = v___y_1022_;
v___y_991_ = v___y_1023_;
v___y_992_ = v___y_1024_;
v___y_993_ = v___y_1026_;
v_hint_994_ = v___x_1027_;
v___y_995_ = v___y_1025_;
v___y_996_ = v___y_1020_;
goto v___jp_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v___f_1260_, lean_object* v_declName_1261_, lean_object* v_stx_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(v___x_1258_, v___x_1259_, v___f_1260_, v_declName_1261_, v_stx_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(uint8_t v___x_1267_, lean_object* v_env_1268_, lean_object* v_n_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Lean_Environment_contains(v_env_1268_, v_n_1269_, v___x_1267_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object* v___x_1272_, lean_object* v_env_1273_, lean_object* v_n_1274_, lean_object* v_x_1275_){
_start:
{
uint8_t v___x_17883__boxed_1276_; uint8_t v_res_1277_; lean_object* v_r_1278_; 
v___x_17883__boxed_1276_ = lean_unbox(v___x_1272_);
v_res_1277_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(v___x_17883__boxed_1276_, v_env_1273_, v_n_1274_, v_x_1275_);
lean_dec_ref(v_x_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_1309_ = l_Lean_registerParametricAttribute___redArg(v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2____boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___redArg(v_msg_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__0(v_00_u03b1_1318_, v_msg_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8(lean_object* v_o_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___redArg(v_o_1324_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8___boxed(lean_object* v_o_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__3_spec__8(v_o_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_00_u03b2_1334_, lean_object* v_m_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_1335_, v_a_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_1338_, v_m_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_m_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___redArg(v_x_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint8_t v_res_1349_; lean_object* v_r_1350_; 
v_res_1349_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_00_u03b2_1346_, v_x_1347_, v_x_1348_);
lean_dec_ref(v_x_1348_);
lean_dec_ref(v_x_1347_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_00_u03b2_1351_, lean_object* v_a_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___redArg(v_a_1352_, v_x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_00_u03b2_1355_, lean_object* v_a_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_00_u03b2_1355_, v_a_1356_, v_x_1357_);
lean_dec(v_x_1357_);
lean_dec(v_a_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_1359_, lean_object* v_x_1360_, size_t v_x_1361_, lean_object* v_x_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___redArg(v_x_1360_, v_x_1361_, v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
size_t v_x_18022__boxed_1368_; uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_x_18022__boxed_1368_ = lean_unbox_usize(v_x_1366_);
lean_dec(v_x_1366_);
v_res_1369_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11(v_00_u03b2_1364_, v_x_1365_, v_x_18022__boxed_1368_, v_x_1367_);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_x_1365_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_k_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_1372_, v_i_1375_, v_k_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03b2_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_k_1383_){
_start:
{
uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_res_1384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4_spec__7_spec__11_spec__14(v_00_u03b2_1378_, v_keys_1379_, v_vals_1380_, v_heq_1381_, v_i_1382_, v_k_1383_);
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
v___x_1434_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(lean_object* v_msgData_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v_env_1461_; lean_object* v___x_1462_; lean_object* v_mctx_1463_; lean_object* v_lctx_1464_; lean_object* v_options_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1460_ = lean_st_ref_get(v___y_1458_);
v_env_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc_ref(v_env_1461_);
lean_dec(v___x_1460_);
v___x_1462_ = lean_st_ref_get(v___y_1456_);
v_mctx_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc_ref(v_mctx_1463_);
lean_dec(v___x_1462_);
v_lctx_1464_ = lean_ctor_get(v___y_1455_, 2);
v_options_1465_ = lean_ctor_get(v___y_1457_, 2);
lean_inc_ref(v_options_1465_);
lean_inc_ref(v_lctx_1464_);
v___x_1466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1466_, 0, v_env_1461_);
lean_ctor_set(v___x_1466_, 1, v_mctx_1463_);
lean_ctor_set(v___x_1466_, 2, v_lctx_1464_);
lean_ctor_set(v___x_1466_, 3, v_options_1465_);
v___x_1467_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_msgData_1454_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(v_msgData_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(lean_object* v_ref_1476_, lean_object* v_msgData_1477_, uint8_t v_severity_1478_, uint8_t v_isSilent_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; uint8_t v___y_1526_; uint8_t v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; uint8_t v___y_1551_; uint8_t v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; uint8_t v___y_1564_; uint8_t v___x_1569_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; uint8_t v___y_1577_; uint8_t v___y_1579_; uint8_t v___x_1594_; 
v___x_1569_ = 2;
v___x_1594_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1478_, v___x_1569_);
if (v___x_1594_ == 0)
{
v___y_1579_ = v___x_1594_;
goto v___jp_1578_;
}
else
{
uint8_t v___x_1595_; 
lean_inc_ref(v_msgData_1477_);
v___x_1595_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1477_);
v___y_1579_ = v___x_1595_;
goto v___jp_1578_;
}
v___jp_1485_:
{
lean_object* v___x_1495_; lean_object* v_currNamespace_1496_; lean_object* v_openDecls_1497_; lean_object* v_env_1498_; lean_object* v_nextMacroScope_1499_; lean_object* v_ngen_1500_; lean_object* v_auxDeclNGen_1501_; lean_object* v_traceState_1502_; lean_object* v_cache_1503_; lean_object* v_messages_1504_; lean_object* v_infoState_1505_; lean_object* v_snapshotTasks_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1520_; 
v___x_1495_ = lean_st_ref_take(v___y_1494_);
v_currNamespace_1496_ = lean_ctor_get(v___y_1493_, 6);
v_openDecls_1497_ = lean_ctor_get(v___y_1493_, 7);
v_env_1498_ = lean_ctor_get(v___x_1495_, 0);
v_nextMacroScope_1499_ = lean_ctor_get(v___x_1495_, 1);
v_ngen_1500_ = lean_ctor_get(v___x_1495_, 2);
v_auxDeclNGen_1501_ = lean_ctor_get(v___x_1495_, 3);
v_traceState_1502_ = lean_ctor_get(v___x_1495_, 4);
v_cache_1503_ = lean_ctor_get(v___x_1495_, 5);
v_messages_1504_ = lean_ctor_get(v___x_1495_, 6);
v_infoState_1505_ = lean_ctor_get(v___x_1495_, 7);
v_snapshotTasks_1506_ = lean_ctor_get(v___x_1495_, 8);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1508_ = v___x_1495_;
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snapshotTasks_1506_);
lean_inc(v_infoState_1505_);
lean_inc(v_messages_1504_);
lean_inc(v_cache_1503_);
lean_inc(v_traceState_1502_);
lean_inc(v_auxDeclNGen_1501_);
lean_inc(v_ngen_1500_);
lean_inc(v_nextMacroScope_1499_);
lean_inc(v_env_1498_);
lean_dec(v___x_1495_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_inc(v_openDecls_1497_);
lean_inc(v_currNamespace_1496_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_currNamespace_1496_);
lean_ctor_set(v___x_1510_, 1, v_openDecls_1497_);
v___x_1511_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___y_1487_);
lean_inc_ref(v___y_1488_);
lean_inc_ref(v___y_1489_);
v___x_1512_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1512_, 0, v___y_1489_);
lean_ctor_set(v___x_1512_, 1, v___y_1492_);
lean_ctor_set(v___x_1512_, 2, v___y_1491_);
lean_ctor_set(v___x_1512_, 3, v___y_1488_);
lean_ctor_set(v___x_1512_, 4, v___x_1511_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*5, v___y_1486_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*5 + 1, v___y_1490_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*5 + 2, v_isSilent_1479_);
v___x_1513_ = l_Lean_MessageLog_add(v___x_1512_, v_messages_1504_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 6, v___x_1513_);
v___x_1515_ = v___x_1508_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_env_1498_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_nextMacroScope_1499_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_ngen_1500_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_auxDeclNGen_1501_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_traceState_1502_);
lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_cache_1503_);
lean_ctor_set(v_reuseFailAlloc_1519_, 6, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 7, v_infoState_1505_);
lean_ctor_set(v_reuseFailAlloc_1519_, 8, v_snapshotTasks_1506_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_st_ref_set(v___y_1494_, v___x_1515_);
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
v___jp_1521_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1545_; 
v___x_1530_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1477_);
v___x_1531_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(v___x_1530_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1545_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1545_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_inc_ref_n(v___y_1528_, 2);
v___x_1536_ = l_Lean_FileMap_toPosition(v___y_1528_, v___y_1525_);
lean_dec(v___y_1525_);
v___x_1537_ = l_Lean_FileMap_toPosition(v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
v___x_1539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___closed__0));
if (v___y_1527_ == 0)
{
lean_del_object(v___x_1534_);
lean_dec_ref(v___y_1522_);
v___y_1486_ = v___y_1523_;
v___y_1487_ = v_a_1532_;
v___y_1488_ = v___x_1539_;
v___y_1489_ = v___y_1524_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___x_1538_;
v___y_1492_ = v___x_1536_;
v___y_1493_ = v___y_1482_;
v___y_1494_ = v___y_1483_;
goto v___jp_1485_;
}
else
{
uint8_t v___x_1540_; 
lean_inc(v_a_1532_);
v___x_1540_ = l_Lean_MessageData_hasTag(v___y_1522_, v_a_1532_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec_ref_known(v___x_1538_, 1);
lean_dec_ref(v___x_1536_);
lean_dec(v_a_1532_);
v___x_1541_ = lean_box(0);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1541_);
v___x_1543_ = v___x_1534_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
lean_del_object(v___x_1534_);
v___y_1486_ = v___y_1523_;
v___y_1487_ = v_a_1532_;
v___y_1488_ = v___x_1539_;
v___y_1489_ = v___y_1524_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___x_1538_;
v___y_1492_ = v___x_1536_;
v___y_1493_ = v___y_1482_;
v___y_1494_ = v___y_1483_;
goto v___jp_1485_;
}
}
}
}
v___jp_1546_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Syntax_getTailPos_x3f(v___y_1549_, v___y_1548_);
lean_dec(v___y_1549_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v___y_1554_);
v___y_1522_ = v___y_1547_;
v___y_1523_ = v___y_1548_;
v___y_1524_ = v___y_1550_;
v___y_1525_ = v___y_1554_;
v___y_1526_ = v___y_1551_;
v___y_1527_ = v___y_1552_;
v___y_1528_ = v___y_1553_;
v___y_1529_ = v___y_1554_;
goto v___jp_1521_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___y_1522_ = v___y_1547_;
v___y_1523_ = v___y_1548_;
v___y_1524_ = v___y_1550_;
v___y_1525_ = v___y_1554_;
v___y_1526_ = v___y_1551_;
v___y_1527_ = v___y_1552_;
v___y_1528_ = v___y_1553_;
v___y_1529_ = v_val_1556_;
goto v___jp_1521_;
}
}
v___jp_1557_:
{
lean_object* v_ref_1565_; lean_object* v___x_1566_; 
v_ref_1565_ = l_Lean_replaceRef(v_ref_1476_, v___y_1559_);
v___x_1566_ = l_Lean_Syntax_getPos_x3f(v_ref_1565_, v___y_1560_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___y_1547_ = v___y_1558_;
v___y_1548_ = v___y_1560_;
v___y_1549_ = v_ref_1565_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1564_;
v___y_1552_ = v___y_1562_;
v___y_1553_ = v___y_1563_;
v___y_1554_ = v___x_1567_;
goto v___jp_1546_;
}
else
{
lean_object* v_val_1568_; 
v_val_1568_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v___x_1566_, 1);
v___y_1547_ = v___y_1558_;
v___y_1548_ = v___y_1560_;
v___y_1549_ = v_ref_1565_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1564_;
v___y_1552_ = v___y_1562_;
v___y_1553_ = v___y_1563_;
v___y_1554_ = v_val_1568_;
goto v___jp_1546_;
}
}
v___jp_1570_:
{
if (v___y_1577_ == 0)
{
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1576_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v_severity_1478_;
goto v___jp_1557_;
}
else
{
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1576_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___x_1569_;
goto v___jp_1557_;
}
}
v___jp_1578_:
{
if (v___y_1579_ == 0)
{
lean_object* v_fileName_1580_; lean_object* v_fileMap_1581_; lean_object* v_options_1582_; lean_object* v_ref_1583_; uint8_t v_suppressElabErrors_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___f_1587_; uint8_t v___x_1588_; uint8_t v___x_1589_; 
v_fileName_1580_ = lean_ctor_get(v___y_1482_, 0);
v_fileMap_1581_ = lean_ctor_get(v___y_1482_, 1);
v_options_1582_ = lean_ctor_get(v___y_1482_, 2);
v_ref_1583_ = lean_ctor_get(v___y_1482_, 5);
v_suppressElabErrors_1584_ = lean_ctor_get_uint8(v___y_1482_, sizeof(void*)*14 + 1);
v___x_1585_ = lean_box(v___y_1579_);
v___x_1586_ = lean_box(v_suppressElabErrors_1584_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1587_, 0, v___x_1585_);
lean_closure_set(v___f_1587_, 1, v___x_1586_);
v___x_1588_ = 1;
v___x_1589_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1478_, v___x_1588_);
if (v___x_1589_ == 0)
{
v___y_1571_ = v_ref_1583_;
v___y_1572_ = v___f_1587_;
v___y_1573_ = v_fileName_1580_;
v___y_1574_ = v_suppressElabErrors_1584_;
v___y_1575_ = v_fileMap_1581_;
v___y_1576_ = v___y_1579_;
v___y_1577_ = v___x_1589_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = l_Lean_warningAsError;
v___x_1591_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_options_1582_, v___x_1590_);
v___y_1571_ = v_ref_1583_;
v___y_1572_ = v___f_1587_;
v___y_1573_ = v_fileName_1580_;
v___y_1574_ = v_suppressElabErrors_1584_;
v___y_1575_ = v_fileMap_1581_;
v___y_1576_ = v___y_1579_;
v___y_1577_ = v___x_1591_;
goto v___jp_1570_;
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_msgData_1477_);
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_1596_, lean_object* v_msgData_1597_, lean_object* v_severity_1598_, lean_object* v_isSilent_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v_severity_boxed_1605_; uint8_t v_isSilent_boxed_1606_; lean_object* v_res_1607_; 
v_severity_boxed_1605_ = lean_unbox(v_severity_1598_);
v_isSilent_boxed_1606_ = lean_unbox(v_isSilent_1599_);
v_res_1607_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(v_ref_1596_, v_msgData_1597_, v_severity_boxed_1605_, v_isSilent_boxed_1606_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v_ref_1596_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(lean_object* v_msgData_1608_, uint8_t v_severity_1609_, uint8_t v_isSilent_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_ref_1616_; lean_object* v___x_1617_; 
v_ref_1616_ = lean_ctor_get(v___y_1613_, 5);
v___x_1617_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(v_ref_1616_, v_msgData_1608_, v_severity_1609_, v_isSilent_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2___boxed(lean_object* v_msgData_1618_, lean_object* v_severity_1619_, lean_object* v_isSilent_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_severity_boxed_1626_; uint8_t v_isSilent_boxed_1627_; lean_object* v_res_1628_; 
v_severity_boxed_1626_ = lean_unbox(v_severity_1619_);
v_isSilent_boxed_1627_ = lean_unbox(v_isSilent_1620_);
v_res_1628_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(v_msgData_1618_, v_severity_boxed_1626_, v_isSilent_boxed_1627_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(lean_object* v_msgData_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = 1;
v___x_1636_ = 0;
v___x_1637_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(v_msgData_1629_, v___x_1635_, v___x_1636_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1___boxed(lean_object* v_msgData_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(v_msgData_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(lean_object* v_o_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v_env_1649_; lean_object* v___x_1650_; lean_object* v_toEnvExtension_1651_; lean_object* v_asyncMode_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_merged_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1664_; 
v___x_1648_ = lean_st_ref_get(v___y_1646_);
v_env_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc_ref(v_env_1649_);
lean_dec(v___x_1648_);
v___x_1650_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1651_ = lean_ctor_get(v___x_1650_, 0);
v_asyncMode_1652_ = lean_ctor_get(v_toEnvExtension_1651_, 2);
v___x_1653_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1653_, v___x_1650_, v_env_1649_, v_asyncMode_1652_, v___x_1654_);
v_merged_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1655_, 1);
lean_dec(v_unused_1665_);
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_merged_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v_merged_1656_);
lean_ctor_set(v___x_1658_, 0, v_o_1645_);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_o_1645_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_merged_1656_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(lean_object* v_o_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_1666_, v___y_1667_);
lean_dec(v___y_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_options_1675_; lean_object* v___x_1676_; 
v_options_1675_ = lean_ctor_get(v___y_1672_, 2);
lean_inc_ref(v_options_1675_);
v___x_1676_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_1675_, v___y_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1682_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__1(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__0));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__3(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__2));
v___x_1688_ = l_Lean_stringToMessageData(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__5(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__4));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__7(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__6));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__9(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__8));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__11(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__10));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__13(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__12));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__15(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__14));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__17(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__16));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__19(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__18));
v___x_1713_ = l_Lean_MessageData_ofFormat(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__21(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__20));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__23(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__22));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__25(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__24));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__27(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__26));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__29(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__28));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Linter_checkDeprecated___closed__31(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Linter_checkDeprecated___closed__30));
v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated(lean_object* v_declName_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1892_; 
v___x_1738_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1892_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1892_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v_extraMsg_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; 
v___x_1743_ = l_Lean_Linter_linter_deprecated;
v___x_1744_ = l_Lean_Linter_getLinterValue(v___x_1743_, v_a_1739_);
lean_dec(v_a_1739_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
lean_dec(v_declName_1732_);
v___x_1773_ = lean_box(0);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1773_);
v___x_1775_ = v___x_1741_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
else
{
lean_object* v___x_1777_; lean_object* v_env_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = lean_st_ref_get(v_a_1736_);
v_env_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_ref(v_env_1778_);
lean_dec(v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_Linter_instInhabitedDeprecationEntry_default));
v___x_1780_ = l_Lean_Linter_deprecatedAttr;
lean_inc(v_declName_1732_);
v___x_1781_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1779_, v___x_1780_, v_env_1778_, v_declName_1732_);
if (lean_obj_tag(v___x_1781_) == 1)
{
lean_object* v_val_1782_; lean_object* v_text_x3f_1783_; 
lean_del_object(v___x_1741_);
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v_text_x3f_1783_ = lean_ctor_get(v_val_1782_, 1);
if (lean_obj_tag(v_text_x3f_1783_) == 0)
{
lean_object* v_newName_x3f_1784_; 
v_newName_x3f_1784_ = lean_ctor_get(v_val_1782_, 0);
lean_inc(v_newName_x3f_1784_);
lean_dec(v_val_1782_);
if (lean_obj_tag(v_newName_x3f_1784_) == 0)
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__spec__2_spec__4___closed__12);
v_extraMsg_1746_ = v___x_1785_;
v___y_1747_ = v_a_1733_;
v___y_1748_ = v_a_1734_;
v___y_1749_ = v_a_1735_;
v___y_1750_ = v_a_1736_;
goto v___jp_1745_;
}
else
{
lean_object* v_val_1786_; lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v_val_1786_ = lean_ctor_get(v_newName_x3f_1784_, 0);
lean_inc_n(v_val_1786_, 2);
lean_dec_ref_known(v_newName_x3f_1784_, 1);
v___x_1787_ = lean_st_ref_get(v_a_1736_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref_n(v_env_1788_, 2);
lean_dec(v___x_1787_);
v___x_1789_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__9, &l_Lean_Linter_checkDeprecated___closed__9_once, _init_l_Lean_Linter_checkDeprecated___closed__9);
v___x_1790_ = l_Lean_MessageData_ofConstName(v_val_1786_, v___x_1744_);
lean_inc_ref(v___x_1790_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__11, &l_Lean_Linter_checkDeprecated___closed__11_once, _init_l_Lean_Linter_checkDeprecated___closed__11);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_Name_getPrefix(v_declName_1732_);
v___x_1795_ = 0;
lean_inc(v_declName_1732_);
v___x_1796_ = l_Lean_Environment_find_x3f(v_env_1788_, v_declName_1732_, v___x_1795_);
if (lean_obj_tag(v___x_1796_) == 1)
{
lean_object* v_val_1797_; lean_object* v___x_1798_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; uint8_t v___y_1825_; uint8_t v___y_1826_; lean_object* v___x_1852_; 
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l_Lean_Name_getPrefix(v_val_1786_);
lean_inc(v_val_1786_);
lean_inc_ref(v_env_1788_);
v___x_1852_ = l_Lean_Environment_find_x3f(v_env_1788_, v_val_1786_, v___x_1795_);
if (lean_obj_tag(v___x_1852_) == 1)
{
lean_object* v_val_1853_; lean_object* v___x_1854_; 
v_val_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_areTypesReduciblyDefEq(v_val_1797_, v_val_1853_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v_msg_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___x_1864_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1864_ = lean_unbox(v_a_1855_);
lean_dec(v_a_1855_);
if (v___x_1864_ == 0)
{
if (v___x_1744_ == 0)
{
lean_dec(v_val_1853_);
lean_dec(v_val_1797_);
v_msg_1857_ = v___x_1793_;
v___y_1858_ = v_a_1733_;
v___y_1859_ = v_a_1734_;
v___y_1860_ = v_a_1735_;
v___y_1861_ = v_a_1736_;
goto v___jp_1856_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1865_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1866_ = l_Lean_ConstantInfo_type(v_val_1853_);
lean_dec(v_val_1853_);
v___x_1867_ = l_Lean_indentExpr(v___x_1866_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1865_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_obj_once(&l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_, &l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_ConstantInfo_type(v_val_1797_);
lean_dec(v_val_1797_);
v___x_1872_ = l_Lean_indentExpr(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1870_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_MessageData_note(v___x_1873_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1793_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v_msg_1857_ = v___x_1875_;
v___y_1858_ = v_a_1733_;
v___y_1859_ = v_a_1734_;
v___y_1860_ = v_a_1735_;
v___y_1861_ = v_a_1736_;
goto v___jp_1856_;
}
}
else
{
lean_dec(v_val_1853_);
lean_dec(v_val_1797_);
v_msg_1857_ = v___x_1793_;
v___y_1858_ = v_a_1733_;
v___y_1859_ = v_a_1734_;
v___y_1860_ = v_a_1735_;
v___y_1861_ = v_a_1736_;
goto v___jp_1856_;
}
v___jp_1856_:
{
uint8_t v___x_1862_; 
v___x_1862_ = l_Lean_Name_isAnonymous(v___x_1794_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_name_eq(v___x_1794_, v___x_1798_);
lean_dec(v___x_1794_);
if (v___x_1863_ == 0)
{
v___y_1820_ = v_msg_1857_;
v___y_1821_ = v___y_1861_;
v___y_1822_ = v___y_1859_;
v___y_1823_ = v___y_1858_;
v___y_1824_ = v___y_1860_;
v___y_1825_ = v___x_1862_;
v___y_1826_ = v___x_1744_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v_msg_1857_;
v___y_1821_ = v___y_1861_;
v___y_1822_ = v___y_1859_;
v___y_1823_ = v___y_1858_;
v___y_1824_ = v___y_1860_;
v___y_1825_ = v___x_1862_;
v___y_1826_ = v___x_1862_;
goto v___jp_1819_;
}
}
else
{
lean_dec(v___x_1798_);
lean_dec(v___x_1794_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
v_extraMsg_1746_ = v_msg_1857_;
v___y_1747_ = v___y_1858_;
v___y_1748_ = v___y_1859_;
v___y_1749_ = v___y_1860_;
v___y_1750_ = v___y_1861_;
goto v___jp_1745_;
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_val_1853_);
lean_dec(v___x_1798_);
lean_dec(v_val_1797_);
lean_dec(v___x_1794_);
lean_dec_ref_known(v___x_1793_, 2);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
lean_dec(v_declName_1732_);
v_a_1876_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1854_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1854_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_dec(v___x_1852_);
lean_dec(v___x_1798_);
lean_dec(v_val_1797_);
lean_dec(v___x_1794_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
v_extraMsg_1746_ = v___x_1793_;
v___y_1747_ = v_a_1733_;
v___y_1748_ = v_a_1734_;
v___y_1749_ = v_a_1735_;
v___y_1750_ = v_a_1736_;
goto v___jp_1745_;
}
v___jp_1799_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1806_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1790_);
v___x_1808_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__13, &l_Lean_Linter_checkDeprecated___closed__13_once, _init_l_Lean_Linter_checkDeprecated___closed__13);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___y_1805_);
v___x_1811_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__15, &l_Lean_Linter_checkDeprecated___closed__15_once, _init_l_Lean_Linter_checkDeprecated___closed__15);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_MessageData_ofName(v___x_1798_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__17, &l_Lean_Linter_checkDeprecated___closed__17_once, _init_l_Lean_Linter_checkDeprecated___closed__17);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_MessageData_note(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___y_1800_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v_extraMsg_1746_ = v___x_1818_;
v___y_1747_ = v___y_1803_;
v___y_1748_ = v___y_1802_;
v___y_1749_ = v___y_1804_;
v___y_1750_ = v___y_1801_;
goto v___jp_1745_;
}
v___jp_1819_:
{
if (v___y_1826_ == 0)
{
uint8_t v___x_1827_; 
lean_inc(v_declName_1732_);
lean_inc_ref(v_env_1788_);
v___x_1827_ = l_Lean_isProtected(v_env_1788_, v_declName_1732_);
if (v___x_1827_ == 0)
{
if (v___x_1744_ == 0)
{
lean_dec(v___x_1798_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
v_extraMsg_1746_ = v___y_1820_;
v___y_1747_ = v___y_1823_;
v___y_1748_ = v___y_1822_;
v___y_1749_ = v___y_1824_;
v___y_1750_ = v___y_1821_;
goto v___jp_1745_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Lean_isProtected(v_env_1788_, v_val_1786_);
if (v___x_1828_ == 0)
{
lean_dec(v___x_1798_);
lean_dec_ref(v___x_1790_);
v_extraMsg_1746_ = v___y_1820_;
v___y_1747_ = v___y_1823_;
v___y_1748_ = v___y_1822_;
v___y_1749_ = v___y_1824_;
v___y_1750_ = v___y_1821_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
lean_inc(v___x_1798_);
v___x_1829_ = l_Lean_Name_componentsRev(v___x_1798_);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = l_List_lengthTR___redArg(v___x_1829_);
v___x_1832_ = lean_nat_dec_lt(v___x_1830_, v___x_1831_);
lean_dec(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_dec(v___x_1829_);
v___x_1833_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__19, &l_Lean_Linter_checkDeprecated___closed__19_once, _init_l_Lean_Linter_checkDeprecated___closed__19);
v___y_1800_ = v___y_1820_;
v___y_1801_ = v___y_1821_;
v___y_1802_ = v___y_1822_;
v___y_1803_ = v___y_1823_;
v___y_1804_ = v___y_1824_;
v___y_1805_ = v___x_1833_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1834_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__21, &l_Lean_Linter_checkDeprecated___closed__21_once, _init_l_Lean_Linter_checkDeprecated___closed__21);
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = l_List_get___redArg(v___x_1829_, v___x_1835_);
lean_dec(v___x_1829_);
v___x_1837_ = l_Lean_MessageData_ofName(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1834_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__23, &l_Lean_Linter_checkDeprecated___closed__23_once, _init_l_Lean_Linter_checkDeprecated___closed__23);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___y_1800_ = v___y_1820_;
v___y_1801_ = v___y_1821_;
v___y_1802_ = v___y_1822_;
v___y_1803_ = v___y_1823_;
v___y_1804_ = v___y_1824_;
v___y_1805_ = v___x_1840_;
goto v___jp_1799_;
}
}
}
}
else
{
lean_dec(v___x_1798_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
v_extraMsg_1746_ = v___y_1820_;
v___y_1747_ = v___y_1823_;
v___y_1748_ = v___y_1822_;
v___y_1749_ = v___y_1824_;
v___y_1750_ = v___y_1821_;
goto v___jp_1745_;
}
}
else
{
lean_dec(v___x_1798_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
if (lean_obj_tag(v_declName_1732_) == 1)
{
lean_object* v_str_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_str_1841_ = lean_ctor_get(v_declName_1732_, 1);
v___x_1842_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__25, &l_Lean_Linter_checkDeprecated___closed__25_once, _init_l_Lean_Linter_checkDeprecated___closed__25);
lean_inc_ref(v_str_1841_);
v___x_1843_ = l_Lean_stringToMessageData(v_str_1841_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__27, &l_Lean_Linter_checkDeprecated___closed__27_once, _init_l_Lean_Linter_checkDeprecated___closed__27);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_MessageData_ofConstName(v_val_1786_, v___y_1825_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__29, &l_Lean_Linter_checkDeprecated___closed__29_once, _init_l_Lean_Linter_checkDeprecated___closed__29);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___y_1761_ = v___y_1820_;
v___y_1762_ = v___y_1821_;
v___y_1763_ = v___y_1822_;
v___y_1764_ = v___y_1823_;
v___y_1765_ = v___y_1824_;
v___y_1766_ = v___x_1850_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_val_1786_);
v___x_1851_ = l_Lean_MessageData_nil;
v___y_1761_ = v___y_1820_;
v___y_1762_ = v___y_1821_;
v___y_1763_ = v___y_1822_;
v___y_1764_ = v___y_1823_;
v___y_1765_ = v___y_1824_;
v___y_1766_ = v___x_1851_;
goto v___jp_1760_;
}
}
}
}
else
{
lean_dec(v___x_1796_);
lean_dec(v___x_1794_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_env_1788_);
lean_dec(v_val_1786_);
v_extraMsg_1746_ = v___x_1793_;
v___y_1747_ = v_a_1733_;
v___y_1748_ = v_a_1734_;
v___y_1749_ = v_a_1735_;
v___y_1750_ = v_a_1736_;
goto v___jp_1745_;
}
}
}
else
{
lean_object* v_val_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_inc_ref(v_text_x3f_1783_);
lean_dec(v_val_1782_);
v_val_1884_ = lean_ctor_get(v_text_x3f_1783_, 0);
lean_inc(v_val_1884_);
lean_dec_ref_known(v_text_x3f_1783_, 1);
v___x_1885_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__31, &l_Lean_Linter_checkDeprecated___closed__31_once, _init_l_Lean_Linter_checkDeprecated___closed__31);
v___x_1886_ = l_Lean_stringToMessageData(v_val_1884_);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v_extraMsg_1746_ = v___x_1887_;
v___y_1747_ = v_a_1733_;
v___y_1748_ = v_a_1734_;
v___y_1749_ = v_a_1735_;
v___y_1750_ = v_a_1736_;
goto v___jp_1745_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_dec(v___x_1781_);
lean_dec(v_declName_1732_);
v___x_1888_ = lean_box(0);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1888_);
v___x_1890_ = v___x_1741_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
v___jp_1745_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_));
v___x_1752_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__1, &l_Lean_Linter_checkDeprecated___closed__1_once, _init_l_Lean_Linter_checkDeprecated___closed__1);
v___x_1753_ = l_Lean_MessageData_ofConstName(v_declName_1732_, v___x_1744_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__3, &l_Lean_Linter_checkDeprecated___closed__3_once, _init_l_Lean_Linter_checkDeprecated___closed__3);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_extraMsg_1746_);
v___x_1758_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1751_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(v___x_1758_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1759_;
}
v___jp_1760_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1767_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__5, &l_Lean_Linter_checkDeprecated___closed__5_once, _init_l_Lean_Linter_checkDeprecated___closed__5);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___y_1766_);
v___x_1769_ = lean_obj_once(&l_Lean_Linter_checkDeprecated___closed__7, &l_Lean_Linter_checkDeprecated___closed__7_once, _init_l_Lean_Linter_checkDeprecated___closed__7);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_MessageData_note(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___y_1761_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v_extraMsg_1746_ = v___x_1772_;
v___y_1747_ = v___y_1764_;
v___y_1748_ = v___y_1763_;
v___y_1749_ = v___y_1765_;
v___y_1750_ = v___y_1762_;
goto v___jp_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkDeprecated___boxed(lean_object* v_declName_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Linter_checkDeprecated(v_declName_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(lean_object* v_o_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_1900_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(lean_object* v_o_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
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
res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_3100820588____hygCtx___hyg_2_();
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
