// Lean compiler output
// Module: Lean.DefEqAttrib
// Imports: public import Lean.Meta.Basic import Lean.Meta.Check import Lean.Meta.WHNF
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "defeqAttrib"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "useBackward"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 237, 34, 130, 157, 80, 121, 174)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 152, 155, 26, 74, 169, 34, 62)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 295, .m_capacity = 295, .m_length = 294, .m_data = "When true, `dsimp` also uses theorems tagged `@[backward_defeq]`, i.e. theorems inferred to be rfl only at default (not instance) transparency. Set this locally (e.g. `set_option backward.defeqAttrib.useBackward true in ...`) to restore the pre-stricter-inference behavior for a specific proof."};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(244, 198, 114, 201, 97, 27, 16, 197)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(150, 188, 13, 64, 239, 38, 217, 135)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 236, 163, 127, 155, 208, 160, 151)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_backward_defeqAttrib_useBackward;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Not a definitional equality: the conclusion should be an equality, but is"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_validateDefEqAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Not a definitional equality: the left-hand side"};
static const lean_object* l_Lean_validateDefEqAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_validateDefEqAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__1;
static const lean_string_object l_Lean_validateDefEqAttr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "\nis not definitionally equal to the right-hand side"};
static const lean_object* l_Lean_validateDefEqAttr___lam__0___closed__2 = (const lean_object*)&l_Lean_validateDefEqAttr___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__3;
static const lean_string_object l_Lean_validateDefEqAttr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed."};
static const lean_object* l_Lean_validateDefEqAttr___lam__0___closed__4 = (const lean_object*)&l_Lean_validateDefEqAttr___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__5;
static lean_once_cell_t l_Lean_validateDefEqAttr___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_validateDefEqAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_validateDefEqAttr___closed__0 = (const lean_object*)&l_Lean_validateDefEqAttr___closed__0_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_validateDefEqAttr___closed__1;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__2;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__3;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__4;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__5;
static const lean_array_object l_Lean_validateDefEqAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_validateDefEqAttr___closed__6 = (const lean_object*)&l_Lean_validateDefEqAttr___closed__6_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__7;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__8;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__9;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__10;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_validateDefEqAttr___closed__11;
static const lean_closure_object l_Lean_validateDefEqAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_validateDefEqAttr___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_validateDefEqAttr___closed__12 = (const lean_object*)&l_Lean_validateDefEqAttr___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "backward_defeq"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 46, 228, 223, 90, 62, 127, 172)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 163, .m_capacity = 163, .m_length = 162, .m_data = "mark theorem as a definitional equality under the permissive pre-stricter-inference rules, used by `dsimp` when `set_option backward.defeqAttrib.useBackward true`"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_validateDefEqAttr___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "backwardDefeqAttr"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 46, 119, 95, 12, 24, 171, 201)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_backwardDefeqAttr;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 863, .m_capacity = 863, .m_length = 862, .m_data = "Marks a theorem as a definitional equality under the permissive transparency rules that\npredated the stricter `@[defeq]` inference (i.e. an equality that holds at `.default` or\n`.all` transparency, but possibly not at `.instances` transparency as required by `dsimp`).\n\nSuch theorems are inferred automatically by `inferDefEqAttr`: any theorem that the old\n`:= rfl` inference would have accepted is tagged `@[backward_defeq]`, and additionally\ntagged `@[defeq]` when it also passes the stricter check at instance transparency.\n\n`dsimp` ignores `@[backward_defeq]` theorems by default. Setting\n`set_option backward.defeqAttrib.useBackward true` (typically scoped to a single proof\nwith `set_option ... in`) makes `dsimp` treat them like `@[defeq]` theorems, which\nprovides a local backwards-compatibility escape hatch for proofs broken by the stricter\ninference.\n"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(91) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "defeq"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 220, 195, 245, 59, 218, 252, 66)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mark theorem as a definitional equality, to be used by `dsimp`"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "defeqAttr"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 101, 216, 69, 252, 98, 163, 179)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_defeqAttr;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 775, .m_capacity = 775, .m_length = 774, .m_data = "Marks the theorem as a definitional equality that can be used by `dsimp`.\n\nThe theorem must be an equality that holds at `.implicit` transparency. A theorem\nwith a definition that is (syntactically) `:= rfl` is implicitly marked `@[defeq]`\n(and also `@[backward_defeq]`, since the latter is a superset); write `:= (rfl)`\ninstead to suppress this.\n\nThe attribute should be given before a `@[simp]` attribute to have effect.\n\nWhen using the module system, an exported theorem can only be `@[defeq]` if all\ndefinitions that need to be unfolded to prove the theorem are exported and exposed.\n\nTagging a theorem with `@[defeq]` automatically also tags it with `@[backward_defeq]`,\nmaintaining the invariant that `@[defeq]` theorems form a subset of `@[backward_defeq]`\ntheorems.\n"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(119) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(111) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(111) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3_value;
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_inferDefEqAttr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_inferDefEqAttr___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_inferDefEqAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Theorem "};
static const lean_object* l_Lean_inferDefEqAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_inferDefEqAttr___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_inferDefEqAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__1;
static const lean_string_object l_Lean_inferDefEqAttr___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = " has a `rfl`-proof but could not be validated as a definitional equality:"};
static const lean_object* l_Lean_inferDefEqAttr___lam__1___closed__2 = (const lean_object*)&l_Lean_inferDefEqAttr___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_inferDefEqAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_inferDefEqAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_inferDefEqAttr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_inferDefEqAttr___closed__0 = (const lean_object*)&l_Lean_inferDefEqAttr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
return v_res_59_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(lean_object* v_opts_60_, lean_object* v_opt_61_){
_start:
{
lean_object* v_name_62_; lean_object* v_defValue_63_; lean_object* v_map_64_; lean_object* v___x_65_; 
v_name_62_ = lean_ctor_get(v_opt_61_, 0);
v_defValue_63_ = lean_ctor_get(v_opt_61_, 1);
v_map_64_ = lean_ctor_get(v_opts_60_, 0);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_64_, v_name_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
uint8_t v___x_66_; 
v___x_66_ = lean_unbox(v_defValue_63_);
return v___x_66_;
}
else
{
lean_object* v_val_67_; 
v_val_67_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_val_67_);
lean_dec_ref_known(v___x_65_, 1);
if (lean_obj_tag(v_val_67_) == 1)
{
uint8_t v_v_68_; 
v_v_68_ = lean_ctor_get_uint8(v_val_67_, 0);
lean_dec_ref_known(v_val_67_, 0);
return v_v_68_;
}
else
{
uint8_t v___x_69_; 
lean_dec(v_val_67_);
v___x_69_ = lean_unbox(v_defValue_63_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(lean_object* v_opts_70_, lean_object* v_opt_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_opts_70_, v_opt_71_);
lean_dec_ref(v_opt_71_);
lean_dec_ref(v_opts_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(lean_object* v_opts_74_, lean_object* v_opt_75_){
_start:
{
lean_object* v_name_76_; lean_object* v_defValue_77_; lean_object* v_map_78_; lean_object* v___x_79_; 
v_name_76_ = lean_ctor_get(v_opt_75_, 0);
v_defValue_77_ = lean_ctor_get(v_opt_75_, 1);
v_map_78_ = lean_ctor_get(v_opts_74_, 0);
v___x_79_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_78_, v_name_76_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_inc(v_defValue_77_);
return v_defValue_77_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_79_, 1);
if (lean_obj_tag(v_val_80_) == 3)
{
lean_object* v_v_81_; 
v_v_81_ = lean_ctor_get(v_val_80_, 0);
lean_inc(v_v_81_);
lean_dec_ref_known(v_val_80_, 1);
return v_v_81_;
}
else
{
lean_dec(v_val_80_);
lean_inc(v_defValue_77_);
return v_defValue_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2___boxed(lean_object* v_opts_82_, lean_object* v_opt_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(v_opts_82_, v_opt_83_);
lean_dec_ref(v_opt_83_);
lean_dec_ref(v_opts_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(lean_object* v_o_88_, lean_object* v_k_89_, uint8_t v_v_90_){
_start:
{
lean_object* v_map_91_; uint8_t v_hasTrace_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_106_; 
v_map_91_ = lean_ctor_get(v_o_88_, 0);
v_hasTrace_92_ = lean_ctor_get_uint8(v_o_88_, sizeof(void*)*1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_o_88_);
if (v_isSharedCheck_106_ == 0)
{
v___x_94_ = v_o_88_;
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_map_91_);
lean_dec(v_o_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_96_, 0, v_v_90_);
lean_inc(v_k_89_);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_89_, v___x_96_, v_map_91_);
if (v_hasTrace_92_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_101_; 
v___x_98_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1));
v___x_99_ = l_Lean_Name_isPrefixOf(v___x_98_, v_k_89_);
lean_dec(v_k_89_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_97_);
v___x_101_ = v___x_94_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_97_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_99_);
return v___x_101_;
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v_k_89_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_97_);
v___x_104_ = v___x_94_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_105_, sizeof(void*)*1, v_hasTrace_92_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___boxed(lean_object* v_o_107_, lean_object* v_k_108_, lean_object* v_v_109_){
_start:
{
uint8_t v_v_boxed_110_; lean_object* v_res_111_; 
v_v_boxed_110_ = lean_unbox(v_v_109_);
v_res_111_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(v_o_107_, v_k_108_, v_v_boxed_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(lean_object* v_opts_112_, lean_object* v_opt_113_, uint8_t v_val_114_){
_start:
{
lean_object* v_name_115_; lean_object* v___x_116_; 
v_name_115_ = lean_ctor_get(v_opt_113_, 0);
lean_inc(v_name_115_);
lean_dec_ref(v_opt_113_);
v___x_116_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(v_opts_112_, v_name_115_, v_val_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(lean_object* v_opts_117_, lean_object* v_opt_118_, lean_object* v_val_119_){
_start:
{
uint8_t v_val_boxed_120_; lean_object* v_res_121_; 
v_val_boxed_120_ = lean_unbox(v_val_119_);
v_res_121_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_opts_117_, v_opt_118_, v_val_boxed_120_);
return v_res_121_;
}
}
static uint64_t _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0(void){
_start:
{
uint8_t v___x_122_; uint64_t v___x_123_; 
v___x_122_ = 1;
v___x_123_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_122_);
return v___x_123_;
}
}
static uint64_t _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1(void){
_start:
{
uint8_t v___x_124_; uint64_t v___x_125_; 
v___x_124_ = 0;
v___x_125_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_126_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object* v_e1_131_, lean_object* v_e2_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_fileName_139_; lean_object* v_fileMap_140_; lean_object* v_options_141_; lean_object* v_currRecDepth_142_; lean_object* v_ref_143_; lean_object* v_currNamespace_144_; lean_object* v_openDecls_145_; lean_object* v_initHeartbeats_146_; lean_object* v_maxHeartbeats_147_; lean_object* v_quotContext_148_; lean_object* v_currMacroScope_149_; lean_object* v_cancelTk_x3f_150_; uint8_t v_suppressElabErrors_151_; lean_object* v_inheritedTraceOptions_152_; lean_object* v_env_153_; uint8_t v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v_fileName_161_; lean_object* v_fileMap_162_; lean_object* v_currRecDepth_163_; lean_object* v_ref_164_; lean_object* v_currNamespace_165_; lean_object* v_openDecls_166_; lean_object* v_initHeartbeats_167_; lean_object* v_maxHeartbeats_168_; lean_object* v_quotContext_169_; lean_object* v_currMacroScope_170_; lean_object* v_cancelTk_x3f_171_; uint8_t v_suppressElabErrors_172_; lean_object* v_inheritedTraceOptions_173_; lean_object* v___y_174_; uint8_t v___y_233_; uint8_t v___x_255_; 
v___x_138_ = lean_st_ref_get(v_a_136_);
v_fileName_139_ = lean_ctor_get(v_a_135_, 0);
v_fileMap_140_ = lean_ctor_get(v_a_135_, 1);
v_options_141_ = lean_ctor_get(v_a_135_, 2);
v_currRecDepth_142_ = lean_ctor_get(v_a_135_, 3);
v_ref_143_ = lean_ctor_get(v_a_135_, 5);
v_currNamespace_144_ = lean_ctor_get(v_a_135_, 6);
v_openDecls_145_ = lean_ctor_get(v_a_135_, 7);
v_initHeartbeats_146_ = lean_ctor_get(v_a_135_, 8);
v_maxHeartbeats_147_ = lean_ctor_get(v_a_135_, 9);
v_quotContext_148_ = lean_ctor_get(v_a_135_, 10);
v_currMacroScope_149_ = lean_ctor_get(v_a_135_, 11);
v_cancelTk_x3f_150_ = lean_ctor_get(v_a_135_, 12);
v_suppressElabErrors_151_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_152_ = lean_ctor_get(v_a_135_, 13);
v_env_153_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_153_);
lean_dec(v___x_138_);
v___x_154_ = 1;
v___x_155_ = l_Lean_Meta_smartUnfolding;
v___x_156_ = 0;
lean_inc_ref(v_options_141_);
v___x_157_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_options_141_, v___x_155_, v___x_156_);
v___x_158_ = l_Lean_diagnostics;
v___x_159_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v___x_157_, v___x_158_);
v___x_255_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_153_);
lean_dec_ref(v_env_153_);
if (v___x_255_ == 0)
{
if (v___x_159_ == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 1;
v___y_233_ = v___x_256_;
goto v___jp_232_;
}
else
{
v___y_233_ = v___x_255_;
goto v___jp_232_;
}
}
else
{
v___y_233_ = v___x_159_;
goto v___jp_232_;
}
v___jp_160_:
{
lean_object* v___x_175_; uint8_t v_foApprox_176_; uint8_t v_ctxApprox_177_; uint8_t v_quasiPatternApprox_178_; uint8_t v_constApprox_179_; uint8_t v_isDefEqStuckEx_180_; uint8_t v_unificationHints_181_; uint8_t v_proofIrrelevance_182_; uint8_t v_assignSyntheticOpaque_183_; uint8_t v_offsetCnstrs_184_; uint8_t v_etaStruct_185_; uint8_t v_univApprox_186_; uint8_t v_iota_187_; uint8_t v_beta_188_; uint8_t v_proj_189_; uint8_t v_zeta_190_; uint8_t v_zetaDelta_191_; uint8_t v_zetaUnused_192_; uint8_t v_zetaHave_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_231_; 
v___x_175_ = l_Lean_Meta_Context_config(v_a_133_);
v_foApprox_176_ = lean_ctor_get_uint8(v___x_175_, 0);
v_ctxApprox_177_ = lean_ctor_get_uint8(v___x_175_, 1);
v_quasiPatternApprox_178_ = lean_ctor_get_uint8(v___x_175_, 2);
v_constApprox_179_ = lean_ctor_get_uint8(v___x_175_, 3);
v_isDefEqStuckEx_180_ = lean_ctor_get_uint8(v___x_175_, 4);
v_unificationHints_181_ = lean_ctor_get_uint8(v___x_175_, 5);
v_proofIrrelevance_182_ = lean_ctor_get_uint8(v___x_175_, 6);
v_assignSyntheticOpaque_183_ = lean_ctor_get_uint8(v___x_175_, 7);
v_offsetCnstrs_184_ = lean_ctor_get_uint8(v___x_175_, 8);
v_etaStruct_185_ = lean_ctor_get_uint8(v___x_175_, 10);
v_univApprox_186_ = lean_ctor_get_uint8(v___x_175_, 11);
v_iota_187_ = lean_ctor_get_uint8(v___x_175_, 12);
v_beta_188_ = lean_ctor_get_uint8(v___x_175_, 13);
v_proj_189_ = lean_ctor_get_uint8(v___x_175_, 14);
v_zeta_190_ = lean_ctor_get_uint8(v___x_175_, 15);
v_zetaDelta_191_ = lean_ctor_get_uint8(v___x_175_, 16);
v_zetaUnused_192_ = lean_ctor_get_uint8(v___x_175_, 17);
v_zetaHave_193_ = lean_ctor_get_uint8(v___x_175_, 18);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_231_ == 0)
{
v___x_195_ = v___x_175_;
v_isShared_196_ = v_isSharedCheck_231_;
goto v_resetjp_194_;
}
else
{
lean_dec(v___x_175_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_231_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
uint8_t v_trackZetaDelta_197_; lean_object* v_zetaDeltaSet_198_; lean_object* v_lctx_199_; lean_object* v_localInstances_200_; lean_object* v_defEqCtx_x3f_201_; lean_object* v_synthPendingDepth_202_; lean_object* v_canUnfold_x3f_203_; uint8_t v_univApprox_204_; uint8_t v_inTypeClassResolution_205_; uint8_t v_cacheInferType_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_config_210_; 
v_trackZetaDelta_197_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*7);
v_zetaDeltaSet_198_ = lean_ctor_get(v_a_133_, 1);
v_lctx_199_ = lean_ctor_get(v_a_133_, 2);
v_localInstances_200_ = lean_ctor_get(v_a_133_, 3);
v_defEqCtx_x3f_201_ = lean_ctor_get(v_a_133_, 4);
v_synthPendingDepth_202_ = lean_ctor_get(v_a_133_, 5);
v_canUnfold_x3f_203_ = lean_ctor_get(v_a_133_, 6);
v_univApprox_204_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_205_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*7 + 2);
v_cacheInferType_206_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*7 + 3);
v___x_207_ = l_Lean_maxRecDepth;
v___x_208_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(v___x_157_, v___x_207_);
if (v_isShared_196_ == 0)
{
v_config_210_ = v___x_195_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 0, v_foApprox_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 1, v_ctxApprox_177_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 2, v_quasiPatternApprox_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 3, v_constApprox_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 4, v_isDefEqStuckEx_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 5, v_unificationHints_181_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 6, v_proofIrrelevance_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 7, v_assignSyntheticOpaque_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 8, v_offsetCnstrs_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 10, v_etaStruct_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 11, v_univApprox_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 12, v_iota_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 13, v_beta_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 14, v_proj_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 15, v_zeta_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 16, v_zetaDelta_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 17, v_zetaUnused_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, 18, v_zetaHave_193_);
v_config_210_ = v_reuseFailAlloc_230_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; lean_object* v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v_key_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_ctor_set_uint8(v_config_210_, 9, v___x_154_);
v___x_211_ = l_Lean_Meta_Context_configKey(v_a_133_);
v___x_212_ = 3ULL;
v___x_213_ = lean_uint64_shift_right(v___x_211_, v___x_212_);
lean_inc_ref(v_inheritedTraceOptions_173_);
lean_inc(v_cancelTk_x3f_171_);
lean_inc(v_currMacroScope_170_);
lean_inc(v_quotContext_169_);
lean_inc(v_maxHeartbeats_168_);
lean_inc(v_initHeartbeats_167_);
lean_inc(v_openDecls_166_);
lean_inc(v_currNamespace_165_);
lean_inc(v_ref_164_);
lean_inc(v_currRecDepth_163_);
lean_inc_ref(v_fileMap_162_);
lean_inc_ref(v_fileName_161_);
v___x_214_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_214_, 0, v_fileName_161_);
lean_ctor_set(v___x_214_, 1, v_fileMap_162_);
lean_ctor_set(v___x_214_, 2, v___x_157_);
lean_ctor_set(v___x_214_, 3, v_currRecDepth_163_);
lean_ctor_set(v___x_214_, 4, v___x_208_);
lean_ctor_set(v___x_214_, 5, v_ref_164_);
lean_ctor_set(v___x_214_, 6, v_currNamespace_165_);
lean_ctor_set(v___x_214_, 7, v_openDecls_166_);
lean_ctor_set(v___x_214_, 8, v_initHeartbeats_167_);
lean_ctor_set(v___x_214_, 9, v_maxHeartbeats_168_);
lean_ctor_set(v___x_214_, 10, v_quotContext_169_);
lean_ctor_set(v___x_214_, 11, v_currMacroScope_170_);
lean_ctor_set(v___x_214_, 12, v_cancelTk_x3f_171_);
lean_ctor_set(v___x_214_, 13, v_inheritedTraceOptions_173_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*14, v___x_159_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*14 + 1, v_suppressElabErrors_172_);
v___x_215_ = lean_uint64_shift_left(v___x_213_, v___x_212_);
v___x_216_ = lean_uint64_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v_key_217_ = lean_uint64_lor(v___x_215_, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_218_, 0, v_config_210_);
lean_ctor_set_uint64(v___x_218_, sizeof(void*)*1, v_key_217_);
lean_inc(v_canUnfold_x3f_203_);
lean_inc(v_synthPendingDepth_202_);
lean_inc(v_defEqCtx_x3f_201_);
lean_inc_ref(v_localInstances_200_);
lean_inc_ref(v_lctx_199_);
lean_inc(v_zetaDeltaSet_198_);
v___x_219_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_zetaDeltaSet_198_);
lean_ctor_set(v___x_219_, 2, v_lctx_199_);
lean_ctor_set(v___x_219_, 3, v_localInstances_200_);
lean_ctor_set(v___x_219_, 4, v_defEqCtx_x3f_201_);
lean_ctor_set(v___x_219_, 5, v_synthPendingDepth_202_);
lean_ctor_set(v___x_219_, 6, v_canUnfold_x3f_203_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*7, v_trackZetaDelta_197_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*7 + 1, v_univApprox_204_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*7 + 2, v_inTypeClassResolution_205_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*7 + 3, v_cacheInferType_206_);
lean_inc_ref(v_e2_132_);
lean_inc_ref(v_e1_131_);
v___x_220_ = l_Lean_Meta_isExprDefEq(v_e1_131_, v_e2_132_, v___x_219_, v_a_134_, v___x_214_, v___y_174_);
lean_dec_ref_known(v___x_219_, 7);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; uint8_t v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
v___x_222_ = lean_unbox(v_a_221_);
lean_dec(v_a_221_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; lean_object* v_config_224_; uint64_t v___x_225_; uint64_t v_key_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref_known(v___x_220_, 1);
v___x_223_ = 0;
v_config_224_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_config_224_, 0, v_foApprox_176_);
lean_ctor_set_uint8(v_config_224_, 1, v_ctxApprox_177_);
lean_ctor_set_uint8(v_config_224_, 2, v_quasiPatternApprox_178_);
lean_ctor_set_uint8(v_config_224_, 3, v_constApprox_179_);
lean_ctor_set_uint8(v_config_224_, 4, v_isDefEqStuckEx_180_);
lean_ctor_set_uint8(v_config_224_, 5, v_unificationHints_181_);
lean_ctor_set_uint8(v_config_224_, 6, v_proofIrrelevance_182_);
lean_ctor_set_uint8(v_config_224_, 7, v_assignSyntheticOpaque_183_);
lean_ctor_set_uint8(v_config_224_, 8, v_offsetCnstrs_184_);
lean_ctor_set_uint8(v_config_224_, 9, v___x_223_);
lean_ctor_set_uint8(v_config_224_, 10, v_etaStruct_185_);
lean_ctor_set_uint8(v_config_224_, 11, v_univApprox_186_);
lean_ctor_set_uint8(v_config_224_, 12, v_iota_187_);
lean_ctor_set_uint8(v_config_224_, 13, v_beta_188_);
lean_ctor_set_uint8(v_config_224_, 14, v_proj_189_);
lean_ctor_set_uint8(v_config_224_, 15, v_zeta_190_);
lean_ctor_set_uint8(v_config_224_, 16, v_zetaDelta_191_);
lean_ctor_set_uint8(v_config_224_, 17, v_zetaUnused_192_);
lean_ctor_set_uint8(v_config_224_, 18, v_zetaHave_193_);
v___x_225_ = lean_uint64_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v_key_226_ = lean_uint64_lor(v___x_215_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_227_, 0, v_config_224_);
lean_ctor_set_uint64(v___x_227_, sizeof(void*)*1, v_key_226_);
lean_inc(v_canUnfold_x3f_203_);
lean_inc(v_synthPendingDepth_202_);
lean_inc(v_defEqCtx_x3f_201_);
lean_inc_ref(v_localInstances_200_);
lean_inc_ref(v_lctx_199_);
lean_inc(v_zetaDeltaSet_198_);
v___x_228_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_zetaDeltaSet_198_);
lean_ctor_set(v___x_228_, 2, v_lctx_199_);
lean_ctor_set(v___x_228_, 3, v_localInstances_200_);
lean_ctor_set(v___x_228_, 4, v_defEqCtx_x3f_201_);
lean_ctor_set(v___x_228_, 5, v_synthPendingDepth_202_);
lean_ctor_set(v___x_228_, 6, v_canUnfold_x3f_203_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*7, v_trackZetaDelta_197_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*7 + 1, v_univApprox_204_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*7 + 2, v_inTypeClassResolution_205_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*7 + 3, v_cacheInferType_206_);
v___x_229_ = l_Lean_Meta_isExprDefEq(v_e1_131_, v_e2_132_, v___x_228_, v_a_134_, v___x_214_, v___y_174_);
lean_dec_ref_known(v___x_214_, 14);
lean_dec_ref_known(v___x_228_, 7);
return v___x_229_;
}
else
{
lean_dec_ref_known(v___x_214_, 14);
lean_dec_ref(v_e2_132_);
lean_dec_ref(v_e1_131_);
return v___x_220_;
}
}
else
{
lean_dec_ref_known(v___x_214_, 14);
lean_dec_ref(v_e2_132_);
lean_dec_ref(v_e1_131_);
return v___x_220_;
}
}
}
}
v___jp_232_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_bool_not(v___y_233_);
if (v___x_234_ == 0)
{
v_fileName_161_ = v_fileName_139_;
v_fileMap_162_ = v_fileMap_140_;
v_currRecDepth_163_ = v_currRecDepth_142_;
v_ref_164_ = v_ref_143_;
v_currNamespace_165_ = v_currNamespace_144_;
v_openDecls_166_ = v_openDecls_145_;
v_initHeartbeats_167_ = v_initHeartbeats_146_;
v_maxHeartbeats_168_ = v_maxHeartbeats_147_;
v_quotContext_169_ = v_quotContext_148_;
v_currMacroScope_170_ = v_currMacroScope_149_;
v_cancelTk_x3f_171_ = v_cancelTk_x3f_150_;
v_suppressElabErrors_172_ = v_suppressElabErrors_151_;
v_inheritedTraceOptions_173_ = v_inheritedTraceOptions_152_;
v___y_174_ = v_a_136_;
goto v___jp_160_;
}
else
{
lean_object* v___x_235_; lean_object* v_env_236_; lean_object* v_nextMacroScope_237_; lean_object* v_ngen_238_; lean_object* v_auxDeclNGen_239_; lean_object* v_traceState_240_; lean_object* v_messages_241_; lean_object* v_infoState_242_; lean_object* v_snapshotTasks_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_253_; 
v___x_235_ = lean_st_ref_take(v_a_136_);
v_env_236_ = lean_ctor_get(v___x_235_, 0);
v_nextMacroScope_237_ = lean_ctor_get(v___x_235_, 1);
v_ngen_238_ = lean_ctor_get(v___x_235_, 2);
v_auxDeclNGen_239_ = lean_ctor_get(v___x_235_, 3);
v_traceState_240_ = lean_ctor_get(v___x_235_, 4);
v_messages_241_ = lean_ctor_get(v___x_235_, 6);
v_infoState_242_ = lean_ctor_get(v___x_235_, 7);
v_snapshotTasks_243_ = lean_ctor_get(v___x_235_, 8);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v___x_235_, 5);
lean_dec(v_unused_254_);
v___x_245_ = v___x_235_;
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snapshotTasks_243_);
lean_inc(v_infoState_242_);
lean_inc(v_messages_241_);
lean_inc(v_traceState_240_);
lean_inc(v_auxDeclNGen_239_);
lean_inc(v_ngen_238_);
lean_inc(v_nextMacroScope_237_);
lean_inc(v_env_236_);
lean_dec(v___x_235_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = l_Lean_Kernel_enableDiag(v_env_236_, v___x_159_);
v___x_248_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 5, v___x_248_);
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_nextMacroScope_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_ngen_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_auxDeclNGen_239_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_traceState_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_messages_241_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_infoState_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_snapshotTasks_243_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; 
v___x_251_ = lean_st_ref_set(v_a_136_, v___x_250_);
v_fileName_161_ = v_fileName_139_;
v_fileMap_162_ = v_fileMap_140_;
v_currRecDepth_163_ = v_currRecDepth_142_;
v_ref_164_ = v_ref_143_;
v_currNamespace_165_ = v_currNamespace_144_;
v_openDecls_166_ = v_openDecls_145_;
v_initHeartbeats_167_ = v_initHeartbeats_146_;
v_maxHeartbeats_168_ = v_maxHeartbeats_147_;
v_quotContext_169_ = v_quotContext_148_;
v_currMacroScope_170_ = v_currMacroScope_149_;
v_cancelTk_x3f_171_ = v_cancelTk_x3f_150_;
v_suppressElabErrors_172_ = v_suppressElabErrors_151_;
v_inheritedTraceOptions_173_ = v_inheritedTraceOptions_152_;
v___y_174_ = v_a_136_;
goto v___jp_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(lean_object* v_e1_257_, lean_object* v_e2_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_e1_257_, v_e2_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(lean_object* v_k_265_, lean_object* v_b_266_, lean_object* v_c_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; 
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
v___x_273_ = lean_apply_7(v_k_265_, v_b_266_, v_c_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, lean_box(0));
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(lean_object* v_k_274_, lean_object* v_b_275_, lean_object* v_c_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_274_, v_b_275_, v_c_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(lean_object* v_type_283_, lean_object* v_k_284_, uint8_t v_cleanupAnnotations_285_, uint8_t v_whnfType_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; 
v___f_292_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_292_, 0, v_k_284_);
v___x_293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_283_, v___f_292_, v_cleanupAnnotations_285_, v_whnfType_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_293_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_293_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(lean_object* v_type_310_, lean_object* v_k_311_, lean_object* v_cleanupAnnotations_312_, lean_object* v_whnfType_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_319_; uint8_t v_whnfType_boxed_320_; lean_object* v_res_321_; 
v_cleanupAnnotations_boxed_319_ = lean_unbox(v_cleanupAnnotations_312_);
v_whnfType_boxed_320_ = lean_unbox(v_whnfType_313_);
v_res_321_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_310_, v_k_311_, v_cleanupAnnotations_boxed_319_, v_whnfType_boxed_320_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_object* v_00_u03b1_322_, lean_object* v_type_323_, lean_object* v_k_324_, uint8_t v_cleanupAnnotations_325_, uint8_t v_whnfType_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_323_, v_k_324_, v_cleanupAnnotations_325_, v_whnfType_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(lean_object* v_00_u03b1_333_, lean_object* v_type_334_, lean_object* v_k_335_, lean_object* v_cleanupAnnotations_336_, lean_object* v_whnfType_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_343_; uint8_t v_whnfType_boxed_344_; lean_object* v_res_345_; 
v_cleanupAnnotations_boxed_343_ = lean_unbox(v_cleanupAnnotations_336_);
v_whnfType_boxed_344_ = lean_unbox(v_whnfType_337_);
v_res_345_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(v_00_u03b1_333_, v_type_334_, v_k_335_, v_cleanupAnnotations_boxed_343_, v_whnfType_boxed_344_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v___x_354_; lean_object* v_mctx_355_; lean_object* v_lctx_356_; lean_object* v_options_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_352_ = lean_st_ref_get(v___y_350_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_env_353_);
lean_dec(v___x_352_);
v___x_354_ = lean_st_ref_get(v___y_348_);
v_mctx_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_ref(v_mctx_355_);
lean_dec(v___x_354_);
v_lctx_356_ = lean_ctor_get(v___y_347_, 2);
v_options_357_ = lean_ctor_get(v___y_349_, 2);
lean_inc_ref(v_options_357_);
lean_inc_ref(v_lctx_356_);
v___x_358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_358_, 0, v_env_353_);
lean_ctor_set(v___x_358_, 1, v_mctx_355_);
lean_ctor_set(v___x_358_, 2, v_lctx_356_);
lean_ctor_set(v___x_358_, 3, v_options_357_);
v___x_359_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_msgData_346_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(lean_object* v_msg_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_ref_374_; lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_ref_374_ = lean_ctor_get(v___y_371_, 5);
v___x_375_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msg_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_inc(v_ref_374_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_ref_374_);
lean_ctor_set(v___x_380_, 1, v_a_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 1);
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(lean_object* v_k_398_, lean_object* v_x_399_, lean_object* v_type_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
v___x_406_ = lean_whnf(v_type_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_409_ = lean_unsigned_to_nat(3u);
v___x_410_ = l_Lean_Expr_isAppOfArity(v_a_407_, v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_k_398_);
v___x_411_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3);
v___x_412_ = lean_unsigned_to_nat(30u);
v___x_413_ = l_Lean_inlineExpr(v_a_407_, v___x_412_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_411_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_414_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = l_Lean_Expr_appFn_x21(v_a_407_);
v___x_417_ = l_Lean_Expr_appArg_x21(v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = l_Lean_Expr_appArg_x21(v_a_407_);
lean_dec(v_a_407_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
v___x_419_ = lean_apply_7(v_k_398_, v___x_417_, v___x_418_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, lean_box(0));
return v___x_419_;
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref(v_k_398_);
v_a_420_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_406_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_406_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(lean_object* v_k_428_, lean_object* v_x_429_, lean_object* v_type_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(v_k_428_, v_x_429_, v_type_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_x_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(lean_object* v_type_437_, lean_object* v_k_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; uint8_t v_foApprox_445_; uint8_t v_ctxApprox_446_; uint8_t v_quasiPatternApprox_447_; uint8_t v_constApprox_448_; uint8_t v_isDefEqStuckEx_449_; uint8_t v_unificationHints_450_; uint8_t v_proofIrrelevance_451_; uint8_t v_assignSyntheticOpaque_452_; uint8_t v_offsetCnstrs_453_; uint8_t v_etaStruct_454_; uint8_t v_univApprox_455_; uint8_t v_iota_456_; uint8_t v_beta_457_; uint8_t v_proj_458_; uint8_t v_zeta_459_; uint8_t v_zetaDelta_460_; uint8_t v_zetaUnused_461_; uint8_t v_zetaHave_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_491_; 
v___x_444_ = l_Lean_Meta_Context_config(v_a_439_);
v_foApprox_445_ = lean_ctor_get_uint8(v___x_444_, 0);
v_ctxApprox_446_ = lean_ctor_get_uint8(v___x_444_, 1);
v_quasiPatternApprox_447_ = lean_ctor_get_uint8(v___x_444_, 2);
v_constApprox_448_ = lean_ctor_get_uint8(v___x_444_, 3);
v_isDefEqStuckEx_449_ = lean_ctor_get_uint8(v___x_444_, 4);
v_unificationHints_450_ = lean_ctor_get_uint8(v___x_444_, 5);
v_proofIrrelevance_451_ = lean_ctor_get_uint8(v___x_444_, 6);
v_assignSyntheticOpaque_452_ = lean_ctor_get_uint8(v___x_444_, 7);
v_offsetCnstrs_453_ = lean_ctor_get_uint8(v___x_444_, 8);
v_etaStruct_454_ = lean_ctor_get_uint8(v___x_444_, 10);
v_univApprox_455_ = lean_ctor_get_uint8(v___x_444_, 11);
v_iota_456_ = lean_ctor_get_uint8(v___x_444_, 12);
v_beta_457_ = lean_ctor_get_uint8(v___x_444_, 13);
v_proj_458_ = lean_ctor_get_uint8(v___x_444_, 14);
v_zeta_459_ = lean_ctor_get_uint8(v___x_444_, 15);
v_zetaDelta_460_ = lean_ctor_get_uint8(v___x_444_, 16);
v_zetaUnused_461_ = lean_ctor_get_uint8(v___x_444_, 17);
v_zetaHave_462_ = lean_ctor_get_uint8(v___x_444_, 18);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_491_ == 0)
{
v___x_464_ = v___x_444_;
v_isShared_465_ = v_isSharedCheck_491_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_444_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_491_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v_trackZetaDelta_466_; lean_object* v_zetaDeltaSet_467_; lean_object* v_lctx_468_; lean_object* v_localInstances_469_; lean_object* v_defEqCtx_x3f_470_; lean_object* v_synthPendingDepth_471_; lean_object* v_canUnfold_x3f_472_; uint8_t v_univApprox_473_; uint8_t v_inTypeClassResolution_474_; uint8_t v_cacheInferType_475_; uint8_t v___x_476_; lean_object* v_config_478_; 
v_trackZetaDelta_466_ = lean_ctor_get_uint8(v_a_439_, sizeof(void*)*7);
v_zetaDeltaSet_467_ = lean_ctor_get(v_a_439_, 1);
v_lctx_468_ = lean_ctor_get(v_a_439_, 2);
v_localInstances_469_ = lean_ctor_get(v_a_439_, 3);
v_defEqCtx_x3f_470_ = lean_ctor_get(v_a_439_, 4);
v_synthPendingDepth_471_ = lean_ctor_get(v_a_439_, 5);
v_canUnfold_x3f_472_ = lean_ctor_get(v_a_439_, 6);
v_univApprox_473_ = lean_ctor_get_uint8(v_a_439_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_474_ = lean_ctor_get_uint8(v_a_439_, sizeof(void*)*7 + 2);
v_cacheInferType_475_ = lean_ctor_get_uint8(v_a_439_, sizeof(void*)*7 + 3);
v___x_476_ = 0;
if (v_isShared_465_ == 0)
{
v_config_478_ = v___x_464_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 0, v_foApprox_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 1, v_ctxApprox_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 2, v_quasiPatternApprox_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 3, v_constApprox_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 4, v_isDefEqStuckEx_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 5, v_unificationHints_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 6, v_proofIrrelevance_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 7, v_assignSyntheticOpaque_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 8, v_offsetCnstrs_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 10, v_etaStruct_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 11, v_univApprox_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 12, v_iota_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 13, v_beta_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 14, v_proj_458_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 15, v_zeta_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 16, v_zetaDelta_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 17, v_zetaUnused_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, 18, v_zetaHave_462_);
v_config_478_ = v_reuseFailAlloc_490_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; lean_object* v___f_482_; uint8_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v_key_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_ctor_set_uint8(v_config_478_, 9, v___x_476_);
v___x_479_ = l_Lean_Meta_Context_configKey(v_a_439_);
v___x_480_ = 3ULL;
v___x_481_ = lean_uint64_shift_right(v___x_479_, v___x_480_);
v___f_482_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_482_, 0, v_k_438_);
v___x_483_ = 0;
v___x_484_ = lean_uint64_shift_left(v___x_481_, v___x_480_);
v___x_485_ = lean_uint64_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v_key_486_ = lean_uint64_lor(v___x_484_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_487_, 0, v_config_478_);
lean_ctor_set_uint64(v___x_487_, sizeof(void*)*1, v_key_486_);
lean_inc(v_canUnfold_x3f_472_);
lean_inc(v_synthPendingDepth_471_);
lean_inc(v_defEqCtx_x3f_470_);
lean_inc_ref(v_localInstances_469_);
lean_inc_ref(v_lctx_468_);
lean_inc(v_zetaDeltaSet_467_);
v___x_488_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_zetaDeltaSet_467_);
lean_ctor_set(v___x_488_, 2, v_lctx_468_);
lean_ctor_set(v___x_488_, 3, v_localInstances_469_);
lean_ctor_set(v___x_488_, 4, v_defEqCtx_x3f_470_);
lean_ctor_set(v___x_488_, 5, v_synthPendingDepth_471_);
lean_ctor_set(v___x_488_, 6, v_canUnfold_x3f_472_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7, v_trackZetaDelta_466_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 1, v_univApprox_473_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 2, v_inTypeClassResolution_474_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 3, v_cacheInferType_475_);
v___x_489_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_437_, v___f_482_, v___x_483_, v___x_483_, v___x_488_, v_a_440_, v_a_441_, v_a_442_);
lean_dec_ref_known(v___x_488_, 7);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(lean_object* v_type_492_, lean_object* v_k_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_492_, v_k_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_object* v_00_u03b1_500_, lean_object* v_type_501_, lean_object* v_k_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_501_, v_k_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(lean_object* v_00_u03b1_509_, lean_object* v_type_510_, lean_object* v_k_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(v_00_u03b1_509_, v_type_510_, v_k_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_object* v_00_u03b1_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(v_00_u03b1_526_, v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(lean_object* v___y_534_, uint8_t v_isExporting_535_, lean_object* v___x_536_, lean_object* v___y_537_, lean_object* v___x_538_, lean_object* v_a_x3f_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_env_542_; lean_object* v_nextMacroScope_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_traceState_546_; lean_object* v_messages_547_; lean_object* v_infoState_548_; lean_object* v_snapshotTasks_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_574_; 
v___x_541_ = lean_st_ref_take(v___y_534_);
v_env_542_ = lean_ctor_get(v___x_541_, 0);
v_nextMacroScope_543_ = lean_ctor_get(v___x_541_, 1);
v_ngen_544_ = lean_ctor_get(v___x_541_, 2);
v_auxDeclNGen_545_ = lean_ctor_get(v___x_541_, 3);
v_traceState_546_ = lean_ctor_get(v___x_541_, 4);
v_messages_547_ = lean_ctor_get(v___x_541_, 6);
v_infoState_548_ = lean_ctor_get(v___x_541_, 7);
v_snapshotTasks_549_ = lean_ctor_get(v___x_541_, 8);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_541_, 5);
lean_dec(v_unused_575_);
v___x_551_ = v___x_541_;
v_isShared_552_ = v_isSharedCheck_574_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snapshotTasks_549_);
lean_inc(v_infoState_548_);
lean_inc(v_messages_547_);
lean_inc(v_traceState_546_);
lean_inc(v_auxDeclNGen_545_);
lean_inc(v_ngen_544_);
lean_inc(v_nextMacroScope_543_);
lean_inc(v_env_542_);
lean_dec(v___x_541_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_574_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_Environment_setExporting(v_env_542_, v_isExporting_535_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 5, v___x_536_);
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_nextMacroScope_543_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_ngen_544_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_auxDeclNGen_545_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_traceState_546_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_messages_547_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_infoState_548_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_snapshotTasks_549_);
v___x_555_ = v_reuseFailAlloc_573_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_mctx_558_; lean_object* v_zetaDeltaFVarIds_559_; lean_object* v_postponed_560_; lean_object* v_diag_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_571_; 
v___x_556_ = lean_st_ref_set(v___y_534_, v___x_555_);
v___x_557_ = lean_st_ref_take(v___y_537_);
v_mctx_558_ = lean_ctor_get(v___x_557_, 0);
v_zetaDeltaFVarIds_559_ = lean_ctor_get(v___x_557_, 2);
v_postponed_560_ = lean_ctor_get(v___x_557_, 3);
v_diag_561_ = lean_ctor_get(v___x_557_, 4);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_557_, 1);
lean_dec(v_unused_572_);
v___x_563_ = v___x_557_;
v_isShared_564_ = v_isSharedCheck_571_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_diag_561_);
lean_inc(v_postponed_560_);
lean_inc(v_zetaDeltaFVarIds_559_);
lean_inc(v_mctx_558_);
lean_dec(v___x_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_571_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_538_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_mctx_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_zetaDeltaFVarIds_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_postponed_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_diag_561_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_st_ref_set(v___y_537_, v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___y_576_, lean_object* v_isExporting_577_, lean_object* v___x_578_, lean_object* v___y_579_, lean_object* v___x_580_, lean_object* v_a_x3f_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_isExporting_boxed_583_; lean_object* v_res_584_; 
v_isExporting_boxed_583_ = lean_unbox(v_isExporting_577_);
v_res_584_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_576_, v_isExporting_boxed_583_, v___x_578_, v___y_579_, v___x_580_, v_a_x3f_581_);
lean_dec(v_a_x3f_581_);
lean_dec(v___y_579_);
lean_dec(v___y_576_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3);
v___x_586_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_ctor_set(v___x_586_, 2, v___x_585_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
lean_ctor_set(v___x_586_, 4, v___x_585_);
lean_ctor_set(v___x_586_, 5, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object* v_x_587_, uint8_t v_isExporting_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_env_595_; uint8_t v_isExporting_596_; uint8_t v___y_663_; lean_object* v___x_665_; uint8_t v_isModule_666_; uint8_t v___x_667_; 
v___x_594_ = lean_st_ref_get(v___y_592_);
v_env_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc_ref(v_env_595_);
lean_dec(v___x_594_);
v_isExporting_596_ = lean_ctor_get_uint8(v_env_595_, sizeof(void*)*8);
v___x_665_ = l_Lean_Environment_header(v_env_595_);
lean_dec_ref(v_env_595_);
v_isModule_666_ = lean_ctor_get_uint8(v___x_665_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_665_);
v___x_667_ = lean_bool_not(v_isModule_666_);
if (v___x_667_ == 0)
{
if (v_isExporting_596_ == 0)
{
if (v_isExporting_588_ == 0)
{
lean_object* v___x_668_; 
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
v___x_668_ = lean_apply_5(v_x_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
return v___x_668_;
}
else
{
goto v___jp_597_;
}
}
else
{
v___y_663_ = v_isExporting_588_;
goto v___jp_662_;
}
}
else
{
v___y_663_ = v___x_667_;
goto v___jp_662_;
}
v___jp_597_:
{
lean_object* v___x_598_; lean_object* v_env_599_; lean_object* v_nextMacroScope_600_; lean_object* v_ngen_601_; lean_object* v_auxDeclNGen_602_; lean_object* v_traceState_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_660_; 
v___x_598_ = lean_st_ref_take(v___y_592_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
v_nextMacroScope_600_ = lean_ctor_get(v___x_598_, 1);
v_ngen_601_ = lean_ctor_get(v___x_598_, 2);
v_auxDeclNGen_602_ = lean_ctor_get(v___x_598_, 3);
v_traceState_603_ = lean_ctor_get(v___x_598_, 4);
v_messages_604_ = lean_ctor_get(v___x_598_, 6);
v_infoState_605_ = lean_ctor_get(v___x_598_, 7);
v_snapshotTasks_606_ = lean_ctor_get(v___x_598_, 8);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_598_, 5);
lean_dec(v_unused_661_);
v___x_608_ = v___x_598_;
v_isShared_609_ = v_isSharedCheck_660_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_traceState_603_);
lean_inc(v_auxDeclNGen_602_);
lean_inc(v_ngen_601_);
lean_inc(v_nextMacroScope_600_);
lean_inc(v_env_599_);
lean_dec(v___x_598_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_660_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = l_Lean_Environment_setExporting(v_env_599_, v_isExporting_588_);
v___x_611_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 5, v___x_611_);
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_nextMacroScope_600_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_ngen_601_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_auxDeclNGen_602_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_traceState_603_);
lean_ctor_set(v_reuseFailAlloc_659_, 5, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_659_, 6, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_659_, 7, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_659_, 8, v_snapshotTasks_606_);
v___x_613_ = v_reuseFailAlloc_659_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_mctx_616_; lean_object* v_zetaDeltaFVarIds_617_; lean_object* v_postponed_618_; lean_object* v_diag_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_657_; 
v___x_614_ = lean_st_ref_set(v___y_592_, v___x_613_);
v___x_615_ = lean_st_ref_take(v___y_590_);
v_mctx_616_ = lean_ctor_get(v___x_615_, 0);
v_zetaDeltaFVarIds_617_ = lean_ctor_get(v___x_615_, 2);
v_postponed_618_ = lean_ctor_get(v___x_615_, 3);
v_diag_619_ = lean_ctor_get(v___x_615_, 4);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_615_, 1);
lean_dec(v_unused_658_);
v___x_621_ = v___x_615_;
v_isShared_622_ = v_isSharedCheck_657_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_diag_619_);
lean_inc(v_postponed_618_);
lean_inc(v_zetaDeltaFVarIds_617_);
lean_inc(v_mctx_616_);
lean_dec(v___x_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_657_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_mctx_616_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_zetaDeltaFVarIds_617_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_postponed_618_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_diag_619_);
v___x_625_ = v_reuseFailAlloc_656_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v_r_627_; 
v___x_626_ = lean_st_ref_set(v___y_590_, v___x_625_);
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
v_r_627_ = lean_apply_5(v_x_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
if (lean_obj_tag(v_r_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_644_; 
v_a_628_ = lean_ctor_get(v_r_627_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_r_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_630_ = v_r_627_;
v_isShared_631_ = v_isSharedCheck_644_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v_r_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_644_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
lean_inc(v_a_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set_tag(v___x_630_, 1);
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_643_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v___x_634_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_592_, v_isExporting_596_, v___x_611_, v___y_590_, v___x_623_, v___x_633_);
lean_dec_ref(v___x_633_);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_642_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_a_628_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_628_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_645_ = lean_ctor_get(v_r_627_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v_r_627_, 1);
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_592_, v_isExporting_596_, v___x_611_, v___y_590_, v___x_623_, v___x_646_);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_647_, 0);
lean_dec(v_unused_655_);
v___x_649_ = v___x_647_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_647_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 1);
lean_ctor_set(v___x_649_, 0, v_a_645_);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_645_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
}
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
goto v___jp_597_;
}
else
{
lean_object* v___x_664_; 
lean_inc(v___y_592_);
lean_inc_ref(v___y_591_);
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
v___x_664_ = lean_apply_5(v_x_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, lean_box(0));
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_669_, lean_object* v_isExporting_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v_isExporting_boxed_676_; lean_object* v_res_677_; 
v_isExporting_boxed_676_ = lean_unbox(v_isExporting_670_);
v_res_677_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_669_, v_isExporting_boxed_676_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object* v_x_678_, uint8_t v_when_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
if (v_when_679_ == 0)
{
lean_object* v___x_685_; 
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
v___x_685_ = lean_apply_5(v_x_678_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, lean_box(0));
return v___x_685_;
}
else
{
uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 0;
v___x_687_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_678_, v___x_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object* v_x_688_, lean_object* v_when_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v_when_boxed_695_; lean_object* v_res_696_; 
v_when_boxed_695_ = lean_unbox(v_when_689_);
v_res_696_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_688_, v_when_boxed_695_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_696_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__0));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__2));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__4));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__5, &l_Lean_validateDefEqAttr___lam__0___closed__5_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__5);
v___x_707_ = l_Lean_MessageData_note(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* v_lhs_708_, lean_object* v_rhs_709_, uint8_t v___x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_lhs_708_, v_rhs_709_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_766_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_766_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_766_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_766_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_765_; 
v_fst_721_ = lean_ctor_get(v_a_717_, 0);
v_snd_722_ = lean_ctor_get(v_a_717_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_a_717_);
if (v_isSharedCheck_765_ == 0)
{
v___x_724_ = v_a_717_;
v_isShared_725_ = v_isSharedCheck_765_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
lean_dec(v_a_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_765_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v_env_727_; uint8_t v_isExporting_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_726_ = lean_st_ref_get(v___y_714_);
v_env_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_env_727_);
lean_dec(v___x_726_);
v_isExporting_728_ = lean_ctor_get_uint8(v_env_727_, sizeof(void*)*8);
lean_dec_ref(v_env_727_);
v___x_729_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__1, &l_Lean_validateDefEqAttr___lam__0___closed__1_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__1);
lean_inc(v_fst_721_);
v___x_730_ = l_Lean_indentExpr(v_fst_721_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 7);
lean_ctor_set(v___x_724_, 1, v___x_730_);
lean_ctor_set(v___x_724_, 0, v___x_729_);
v___x_732_ = v___x_724_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_764_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_733_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__3, &l_Lean_validateDefEqAttr___lam__0___closed__3_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__3);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc(v_snd_722_);
v___x_735_ = l_Lean_indentExpr(v_snd_722_);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
if (v_isExporting_728_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_snd_722_);
lean_dec(v_fst_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_736_);
v___x_738_ = v___x_719_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_719_);
v___x_740_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed), 7, 2);
lean_closure_set(v___x_740_, 0, v_fst_721_);
lean_closure_set(v___x_740_, 1, v_snd_722_);
v___x_741_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___x_740_, v___x_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_755_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_755_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint8_t v___x_746_; 
v___x_746_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
if (v___x_746_ == 0)
{
lean_object* v___x_748_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_736_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_736_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_750_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__6, &l_Lean_validateDefEqAttr___lam__0___closed__6_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__6);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_736_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_751_);
v___x_753_ = v___x_744_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref_known(v___x_736_, 2);
v_a_756_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_741_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_741_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_767_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_716_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_716_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object* v_lhs_775_, lean_object* v_rhs_776_, lean_object* v___x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
uint8_t v___x_6918__boxed_783_; lean_object* v_res_784_; 
v___x_6918__boxed_783_ = lean_unbox(v___x_777_);
v_res_784_ = l_Lean_validateDefEqAttr___lam__0(v_lhs_775_, v_rhs_776_, v___x_6918__boxed_783_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* v_lhs_785_, lean_object* v_rhs_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
lean_inc_ref(v_rhs_786_);
lean_inc_ref(v_lhs_785_);
v___x_792_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_lhs_785_, v_rhs_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_811_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_811_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_811_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
uint8_t v___x_797_; 
v___x_797_ = lean_unbox(v_a_793_);
lean_dec(v_a_793_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_del_object(v___x_795_);
v___x_798_ = 1;
v___x_799_ = lean_box(v___x_798_);
lean_inc_ref(v_rhs_786_);
lean_inc_ref(v_lhs_785_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_800_, 0, v_lhs_785_);
lean_closure_set(v___f_800_, 1, v_rhs_786_);
lean_closure_set(v___f_800_, 2, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(2u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_array_push(v___x_802_, v_lhs_785_);
v___x_804_ = lean_array_push(v___x_803_, v_rhs_786_);
v___x_805_ = l_Lean_MessageData_ofLazyM(v___f_800_, v___x_804_);
v___x_806_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_805_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec_ref(v_rhs_786_);
lean_dec_ref(v_lhs_785_);
v___x_807_ = lean_box(0);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_807_);
v___x_809_ = v___x_795_;
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
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_rhs_786_);
lean_dec_ref(v_lhs_785_);
v_a_812_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_792_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_792_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* v_lhs_820_, lean_object* v_rhs_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_820_, v_rhs_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set(v___x_833_, 2, v___x_832_);
lean_ctor_set(v___x_833_, 3, v___x_832_);
lean_ctor_set(v___x_833_, 4, v___x_831_);
lean_ctor_set(v___x_833_, 5, v___x_831_);
lean_ctor_set(v___x_833_, 6, v___x_831_);
lean_ctor_set(v___x_833_, 7, v___x_831_);
lean_ctor_set(v___x_833_, 8, v___x_831_);
lean_ctor_set(v___x_833_, 9, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_unsigned_to_nat(32u);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_unsigned_to_nat(32u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_842_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_838_);
lean_ctor_set(v___x_842_, 3, v___x_838_);
lean_ctor_set_usize(v___x_842_, 4, v___x_837_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_843_ = lean_box(1);
v___x_844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
lean_ctor_set(v___x_846_, 2, v___x_843_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_868_, lean_object* v_declHint_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; lean_object* v_env_873_; uint8_t v___y_875_; uint8_t v___x_931_; uint8_t v___x_932_; 
v___x_872_ = lean_st_ref_get(v___y_870_);
v_env_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc_ref(v_env_873_);
lean_dec(v___x_872_);
v___x_931_ = l_Lean_Name_isAnonymous(v_declHint_869_);
v___x_932_ = lean_bool_not(v___x_931_);
if (v___x_932_ == 0)
{
v___y_875_ = v___x_932_;
goto v___jp_874_;
}
else
{
uint8_t v_isExporting_933_; 
v_isExporting_933_ = lean_ctor_get_uint8(v_env_873_, sizeof(void*)*8);
v___y_875_ = v_isExporting_933_;
goto v___jp_874_;
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v_env_873_);
lean_dec(v_declHint_869_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_msg_868_);
return v___x_876_;
}
else
{
uint8_t v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = 0;
lean_inc_ref(v_env_873_);
v___x_878_ = l_Lean_Environment_setExporting(v_env_873_, v___x_877_);
lean_inc(v_declHint_869_);
lean_inc_ref(v___x_878_);
v___x_879_ = l_Lean_Environment_contains(v___x_878_, v_declHint_869_, v___y_875_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_env_873_);
lean_dec(v_declHint_869_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_msg_868_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_c_886_; lean_object* v___x_887_; 
v___x_881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_883_ = l_Lean_Options_empty;
v___x_884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_884_, 0, v___x_878_);
lean_ctor_set(v___x_884_, 1, v___x_881_);
lean_ctor_set(v___x_884_, 2, v___x_882_);
lean_ctor_set(v___x_884_, 3, v___x_883_);
lean_inc(v_declHint_869_);
v___x_885_ = l_Lean_MessageData_ofConstName(v_declHint_869_, v___x_877_);
v_c_886_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_886_, 0, v___x_884_);
lean_ctor_set(v_c_886_, 1, v___x_885_);
v___x_887_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_873_, v_declHint_869_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_env_873_);
lean_dec(v_declHint_869_);
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_c_886_);
v___x_890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_MessageData_note(v___x_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v_msg_868_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_930_; 
v_val_895_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_930_ == 0)
{
v___x_897_ = v___x_887_;
v_isShared_898_ = v_isSharedCheck_930_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___x_887_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_930_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_mod_902_; uint8_t v___x_903_; 
v___x_899_ = lean_box(0);
v___x_900_ = l_Lean_Environment_header(v_env_873_);
lean_dec_ref(v_env_873_);
v___x_901_ = l_Lean_EnvironmentHeader_moduleNames(v___x_900_);
v_mod_902_ = lean_array_get(v___x_899_, v___x_901_, v_val_895_);
lean_dec(v_val_895_);
lean_dec_ref(v___x_901_);
v___x_903_ = l_Lean_isPrivateName(v_declHint_869_);
lean_dec(v_declHint_869_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_c_886_);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_MessageData_ofName(v_mod_902_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_MessageData_note(v___x_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v_msg_868_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 0);
lean_ctor_set(v___x_897_, 0, v___x_913_);
v___x_915_ = v___x_897_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_c_886_);
v___x_919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_ofName(v_mod_902_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_MessageData_note(v___x_924_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v_msg_868_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 0);
lean_ctor_set(v___x_897_, 0, v___x_926_);
v___x_928_ = v___x_897_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_934_, lean_object* v_declHint_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_934_, v_declHint_935_, v___y_936_);
lean_dec(v___y_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_939_, lean_object* v_declHint_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_954_; 
v___x_944_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_939_, v_declHint_940_, v___y_942_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_954_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = l_Lean_unknownIdentifierMessageTag;
v___x_950_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_a_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_955_, lean_object* v_declHint_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_955_, v_declHint_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v_options_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_965_ = lean_st_ref_get(v___y_963_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_966_);
lean_dec(v___x_965_);
v_options_967_ = lean_ctor_get(v___y_962_, 2);
v___x_968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_969_ = lean_unsigned_to_nat(32u);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
lean_dec_ref(v___x_970_);
v___x_971_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_967_);
v___x_972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_972_, 0, v_env_966_);
lean_ctor_set(v___x_972_, 1, v___x_968_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_ctor_set(v___x_972_, 3, v_options_967_);
v___x_973_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_msgData_961_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_ref_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_ref_984_ = lean_ctor_get(v___y_981_, 5);
v___x_985_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_980_, v___y_981_, v___y_982_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
lean_inc(v_ref_984_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_ref_984_);
lean_ctor_set(v___x_990_, 1, v_a_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 1);
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1000_, lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_fileName_1005_; lean_object* v_fileMap_1006_; lean_object* v_options_1007_; lean_object* v_currRecDepth_1008_; lean_object* v_maxRecDepth_1009_; lean_object* v_ref_1010_; lean_object* v_currNamespace_1011_; lean_object* v_openDecls_1012_; lean_object* v_initHeartbeats_1013_; lean_object* v_maxHeartbeats_1014_; lean_object* v_quotContext_1015_; lean_object* v_currMacroScope_1016_; uint8_t v_diag_1017_; lean_object* v_cancelTk_x3f_1018_; uint8_t v_suppressElabErrors_1019_; lean_object* v_inheritedTraceOptions_1020_; lean_object* v_ref_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_fileName_1005_ = lean_ctor_get(v___y_1002_, 0);
v_fileMap_1006_ = lean_ctor_get(v___y_1002_, 1);
v_options_1007_ = lean_ctor_get(v___y_1002_, 2);
v_currRecDepth_1008_ = lean_ctor_get(v___y_1002_, 3);
v_maxRecDepth_1009_ = lean_ctor_get(v___y_1002_, 4);
v_ref_1010_ = lean_ctor_get(v___y_1002_, 5);
v_currNamespace_1011_ = lean_ctor_get(v___y_1002_, 6);
v_openDecls_1012_ = lean_ctor_get(v___y_1002_, 7);
v_initHeartbeats_1013_ = lean_ctor_get(v___y_1002_, 8);
v_maxHeartbeats_1014_ = lean_ctor_get(v___y_1002_, 9);
v_quotContext_1015_ = lean_ctor_get(v___y_1002_, 10);
v_currMacroScope_1016_ = lean_ctor_get(v___y_1002_, 11);
v_diag_1017_ = lean_ctor_get_uint8(v___y_1002_, sizeof(void*)*14);
v_cancelTk_x3f_1018_ = lean_ctor_get(v___y_1002_, 12);
v_suppressElabErrors_1019_ = lean_ctor_get_uint8(v___y_1002_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1020_ = lean_ctor_get(v___y_1002_, 13);
v_ref_1021_ = l_Lean_replaceRef(v_ref_1000_, v_ref_1010_);
lean_inc_ref(v_inheritedTraceOptions_1020_);
lean_inc(v_cancelTk_x3f_1018_);
lean_inc(v_currMacroScope_1016_);
lean_inc(v_quotContext_1015_);
lean_inc(v_maxHeartbeats_1014_);
lean_inc(v_initHeartbeats_1013_);
lean_inc(v_openDecls_1012_);
lean_inc(v_currNamespace_1011_);
lean_inc(v_maxRecDepth_1009_);
lean_inc(v_currRecDepth_1008_);
lean_inc_ref(v_options_1007_);
lean_inc_ref(v_fileMap_1006_);
lean_inc_ref(v_fileName_1005_);
v___x_1022_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1022_, 0, v_fileName_1005_);
lean_ctor_set(v___x_1022_, 1, v_fileMap_1006_);
lean_ctor_set(v___x_1022_, 2, v_options_1007_);
lean_ctor_set(v___x_1022_, 3, v_currRecDepth_1008_);
lean_ctor_set(v___x_1022_, 4, v_maxRecDepth_1009_);
lean_ctor_set(v___x_1022_, 5, v_ref_1021_);
lean_ctor_set(v___x_1022_, 6, v_currNamespace_1011_);
lean_ctor_set(v___x_1022_, 7, v_openDecls_1012_);
lean_ctor_set(v___x_1022_, 8, v_initHeartbeats_1013_);
lean_ctor_set(v___x_1022_, 9, v_maxHeartbeats_1014_);
lean_ctor_set(v___x_1022_, 10, v_quotContext_1015_);
lean_ctor_set(v___x_1022_, 11, v_currMacroScope_1016_);
lean_ctor_set(v___x_1022_, 12, v_cancelTk_x3f_1018_);
lean_ctor_set(v___x_1022_, 13, v_inheritedTraceOptions_1020_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*14, v_diag_1017_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*14 + 1, v_suppressElabErrors_1019_);
v___x_1023_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1001_, v___x_1022_, v___y_1003_);
lean_dec_ref_known(v___x_1022_, 14);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1024_, lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1024_, v_msg_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v_ref_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1030_, lean_object* v_msg_1031_, lean_object* v_declHint_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_a_1037_; lean_object* v___x_1038_; 
v___x_1036_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1031_, v_declHint_1032_, v___y_1033_, v___y_1034_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1030_, v_a_1037_, v___y_1033_, v___y_1034_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1039_, lean_object* v_msg_1040_, lean_object* v_declHint_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1039_, v_msg_1040_, v_declHint_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v_ref_1039_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1052_, lean_object* v_constName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1057_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1058_ = 0;
lean_inc(v_constName_1053_);
v___x_1059_ = l_Lean_MessageData_ofConstName(v_constName_1053_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1057_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1052_, v___x_1062_, v_constName_1053_, v___y_1054_, v___y_1055_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1064_, lean_object* v_constName_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1064_, v_constName_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v_ref_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object* v_constName_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_ref_1074_; lean_object* v___x_1075_; 
v_ref_1074_ = lean_ctor_get(v___y_1071_, 5);
v___x_1075_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1074_, v_constName_1070_, v___y_1071_, v___y_1072_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object* v_constName_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_env_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = lean_st_ref_get(v___y_1083_);
v_env_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = 0;
lean_inc(v_constName_1081_);
v___x_1088_ = l_Lean_Environment_findConstVal_x3f(v_env_1086_, v_constName_1081_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1081_, v___y_1082_, v___y_1083_);
return v___x_1089_;
}
else
{
lean_object* v_val_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_constName_1081_);
v_val_1090_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1088_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_val_1090_);
lean_dec(v___x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_val_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object* v_constName_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1102_;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__1(void){
_start:
{
lean_object* v___x_1109_; uint64_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1110_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__2(void){
_start:
{
uint64_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_uint64_once(&l_Lean_validateDefEqAttr___closed__1, &l_Lean_validateDefEqAttr___closed__1_once, _init_l_Lean_validateDefEqAttr___closed__1);
v___x_1112_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1113_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set_uint64(v___x_1113_, sizeof(void*)*1, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3(void){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__3, &l_Lean_validateDefEqAttr___closed__3_once, _init_l_Lean_validateDefEqAttr___closed__3);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_box(1);
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1119_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
lean_ctor_set(v___x_1120_, 2, v___x_1117_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7(void){
_start:
{
uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1123_ = 1;
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_box(0);
v___x_1126_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__6));
v___x_1127_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__5, &l_Lean_validateDefEqAttr___closed__5_once, _init_l_Lean_validateDefEqAttr___closed__5);
v___x_1128_ = lean_box(1);
v___x_1129_ = 0;
v___x_1130_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__2, &l_Lean_validateDefEqAttr___closed__2_once, _init_l_Lean_validateDefEqAttr___closed__2);
v___x_1131_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1128_);
lean_ctor_set(v___x_1131_, 2, v___x_1127_);
lean_ctor_set(v___x_1131_, 3, v___x_1126_);
lean_ctor_set(v___x_1131_, 4, v___x_1125_);
lean_ctor_set(v___x_1131_, 5, v___x_1124_);
lean_ctor_set(v___x_1131_, 6, v___x_1125_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*7, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*7 + 1, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*7 + 2, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*7 + 3, v___x_1123_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
lean_ctor_set(v___x_1134_, 2, v___x_1133_);
lean_ctor_set(v___x_1134_, 3, v___x_1133_);
lean_ctor_set(v___x_1134_, 4, v___x_1132_);
lean_ctor_set(v___x_1134_, 5, v___x_1132_);
lean_ctor_set(v___x_1134_, 6, v___x_1132_);
lean_ctor_set(v___x_1134_, 7, v___x_1132_);
lean_ctor_set(v___x_1134_, 8, v___x_1132_);
lean_ctor_set(v___x_1134_, 9, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
lean_ctor_set(v___x_1136_, 3, v___x_1135_);
lean_ctor_set(v___x_1136_, 4, v___x_1135_);
lean_ctor_set(v___x_1136_, 5, v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
lean_ctor_set(v___x_1138_, 3, v___x_1137_);
lean_ctor_set(v___x_1138_, 4, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__10, &l_Lean_validateDefEqAttr___closed__10_once, _init_l_Lean_validateDefEqAttr___closed__10);
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1141_ = lean_box(1);
v___x_1142_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__9, &l_Lean_validateDefEqAttr___closed__9_once, _init_l_Lean_validateDefEqAttr___closed__9);
v___x_1143_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__8, &l_Lean_validateDefEqAttr___closed__8_once, _init_l_Lean_validateDefEqAttr___closed__8);
v___x_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v___x_1142_);
lean_ctor_set(v___x_1144_, 2, v___x_1141_);
lean_ctor_set(v___x_1144_, 3, v___x_1140_);
lean_ctor_set(v___x_1144_, 4, v___x_1139_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object* v_declName_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_declName_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_type_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__7, &l_Lean_validateDefEqAttr___closed__7_once, _init_l_Lean_validateDefEqAttr___closed__7);
v___x_1153_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__11, &l_Lean_validateDefEqAttr___closed__11_once, _init_l_Lean_validateDefEqAttr___closed__11);
v___x_1154_ = lean_st_mk_ref(v___x_1153_);
v_type_1155_ = lean_ctor_get(v_a_1151_, 2);
lean_inc_ref(v_type_1155_);
lean_dec(v_a_1151_);
v___f_1156_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__12));
v___x_1157_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_1155_, v___f_1156_, v___x_1152_, v___x_1154_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_st_ref_get(v___x_1154_);
lean_dec(v___x_1154_);
lean_dec(v___x_1162_);
if (v_isShared_1161_ == 0)
{
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1158_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_dec(v___x_1154_);
return v___x_1157_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1150_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1150_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object* v_declName_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_validateDefEqAttr(v_declName_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_1180_, lean_object* v_x_1181_, uint8_t v_isExporting_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_1181_, v_isExporting_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_x_1190_, lean_object* v_isExporting_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v_isExporting_boxed_1197_; lean_object* v_res_1198_; 
v_isExporting_boxed_1197_ = lean_unbox(v_isExporting_1191_);
v_res_1198_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_1189_, v_x_1190_, v_isExporting_boxed_1197_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object* v_00_u03b1_1199_, lean_object* v_x_1200_, uint8_t v_when_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_1200_, v_when_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_x_1209_, lean_object* v_when_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_when_boxed_1216_; lean_object* v_res_1217_; 
v_when_boxed_1216_ = lean_unbox(v_when_1210_);
v_res_1217_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(v_00_u03b1_1208_, v_x_1209_, v_when_boxed_1216_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object* v_00_u03b1_1218_, lean_object* v_constName_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1219_, v___y_1220_, v___y_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_constName_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_1224_, v_constName_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1230_, lean_object* v_ref_1231_, lean_object* v_constName_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1231_, v_constName_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_ref_1238_, lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_1237_, v_ref_1238_, v_constName_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v_ref_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1244_, lean_object* v_ref_1245_, lean_object* v_msg_1246_, lean_object* v_declHint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1245_, v_msg_1246_, v_declHint_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_ref_1253_, lean_object* v_msg_1254_, lean_object* v_declHint_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1252_, v_ref_1253_, v_msg_1254_, v_declHint_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v_ref_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1260_, lean_object* v_declHint_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1260_, v_declHint_1261_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1266_, lean_object* v_declHint_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1266_, v_declHint_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1273_, v_msg_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_ref_1280_, lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1279_, v_ref_1280_, v_msg_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v_ref_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1286_, lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1292_, v_msg_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1311_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1312_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1313_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1314_ = 0;
v___x_1315_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1316_ = l_Lean_registerTagAttribute(v___x_1310_, v___x_1311_, v___x_1312_, v___x_1313_, v___x_1314_, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1(){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1322_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0));
v___x_1323_ = l_Lean_addBuiltinDocString(v___x_1321_, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1353_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6));
v___x_1354_ = l_Lean_addBuiltinDeclarationRanges(v___x_1352_, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_attrName_1369_, lean_object* v_declName_1370_, lean_object* v_asyncPrefix_x3f_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___y_1376_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1371_) == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_MessageData_nil;
v___y_1376_ = v___x_1389_;
goto v___jp_1375_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_val_1390_ = lean_ctor_get(v_asyncPrefix_x3f_1371_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v_asyncPrefix_x3f_1371_, 1);
v___x_1391_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1392_ = l_Lean_MessageData_ofName(v_val_1390_);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___y_1376_ = v___x_1395_;
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1377_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1378_ = l_Lean_MessageData_ofName(v_attrName_1369_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = 0;
v___x_1383_ = l_Lean_MessageData_ofConstName(v_declName_1370_, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1381_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v___y_1376_);
v___x_1388_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1387_, v___y_1372_, v___y_1373_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1396_, lean_object* v_declName_1397_, lean_object* v_asyncPrefix_x3f_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1396_, v_declName_1397_, v_asyncPrefix_x3f_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1402_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_attrName_1406_, lean_object* v_declName_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1411_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1412_ = l_Lean_MessageData_ofName(v_attrName_1406_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = 0;
v___x_1417_ = l_Lean_MessageData_ofConstName(v_declName_1407_, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1415_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1420_, v___y_1408_, v___y_1409_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1422_, lean_object* v_declName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1422_, v_declName_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object* v_attr_1428_, lean_object* v_decl_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___y_1434_; lean_object* v___x_1460_; lean_object* v_env_1461_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___x_1474_; 
v___x_1460_ = lean_st_ref_get(v___y_1431_);
v_env_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc_ref(v_env_1461_);
lean_dec(v___x_1460_);
v___x_1474_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1461_, v_decl_1429_);
if (lean_obj_tag(v___x_1474_) == 0)
{
v___y_1463_ = v___y_1430_;
v___y_1464_ = v___y_1431_;
goto v___jp_1462_;
}
else
{
lean_object* v_attr_1475_; lean_object* v_toAttributeImplCore_1476_; lean_object* v_name_1477_; lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1474_, 1);
lean_dec_ref(v_env_1461_);
v_attr_1475_ = lean_ctor_get(v_attr_1428_, 0);
lean_inc_ref(v_attr_1475_);
lean_dec_ref(v_attr_1428_);
v_toAttributeImplCore_1476_ = lean_ctor_get(v_attr_1475_, 0);
lean_inc_ref(v_toAttributeImplCore_1476_);
lean_dec_ref(v_attr_1475_);
v_name_1477_ = lean_ctor_get(v_toAttributeImplCore_1476_, 1);
lean_inc(v_name_1477_);
lean_dec_ref(v_toAttributeImplCore_1476_);
v___x_1478_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_1477_, v_decl_1429_, v___y_1430_, v___y_1431_);
return v___x_1478_;
}
v___jp_1433_:
{
lean_object* v___x_1435_; lean_object* v_ext_1436_; lean_object* v_toEnvExtension_1437_; lean_object* v_env_1438_; lean_object* v_nextMacroScope_1439_; lean_object* v_ngen_1440_; lean_object* v_auxDeclNGen_1441_; lean_object* v_traceState_1442_; lean_object* v_messages_1443_; lean_object* v_infoState_1444_; lean_object* v_snapshotTasks_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1458_; 
v___x_1435_ = lean_st_ref_take(v___y_1434_);
v_ext_1436_ = lean_ctor_get(v_attr_1428_, 1);
lean_inc_ref(v_ext_1436_);
lean_dec_ref(v_attr_1428_);
v_toEnvExtension_1437_ = lean_ctor_get(v_ext_1436_, 0);
v_env_1438_ = lean_ctor_get(v___x_1435_, 0);
v_nextMacroScope_1439_ = lean_ctor_get(v___x_1435_, 1);
v_ngen_1440_ = lean_ctor_get(v___x_1435_, 2);
v_auxDeclNGen_1441_ = lean_ctor_get(v___x_1435_, 3);
v_traceState_1442_ = lean_ctor_get(v___x_1435_, 4);
v_messages_1443_ = lean_ctor_get(v___x_1435_, 6);
v_infoState_1444_ = lean_ctor_get(v___x_1435_, 7);
v_snapshotTasks_1445_ = lean_ctor_get(v___x_1435_, 8);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1435_, 5);
lean_dec(v_unused_1459_);
v___x_1447_ = v___x_1435_;
v_isShared_1448_ = v_isSharedCheck_1458_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_snapshotTasks_1445_);
lean_inc(v_infoState_1444_);
lean_inc(v_messages_1443_);
lean_inc(v_traceState_1442_);
lean_inc(v_auxDeclNGen_1441_);
lean_inc(v_ngen_1440_);
lean_inc(v_nextMacroScope_1439_);
lean_inc(v_env_1438_);
lean_dec(v___x_1435_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1458_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_asyncMode_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v_asyncMode_1449_ = lean_ctor_get(v_toEnvExtension_1437_, 2);
lean_inc(v_asyncMode_1449_);
lean_inc(v_decl_1429_);
v___x_1450_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1436_, v_env_1438_, v_decl_1429_, v_asyncMode_1449_, v_decl_1429_);
lean_dec(v_asyncMode_1449_);
v___x_1451_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 5, v___x_1451_);
lean_ctor_set(v___x_1447_, 0, v___x_1450_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_nextMacroScope_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_ngen_1440_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_auxDeclNGen_1441_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_traceState_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1457_, 6, v_messages_1443_);
lean_ctor_set(v_reuseFailAlloc_1457_, 7, v_infoState_1444_);
lean_ctor_set(v_reuseFailAlloc_1457_, 8, v_snapshotTasks_1445_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_st_ref_set(v___y_1434_, v___x_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
v___jp_1462_:
{
lean_object* v_ext_1465_; lean_object* v_toEnvExtension_1466_; lean_object* v_attr_1467_; lean_object* v_asyncMode_1468_; uint8_t v___x_1469_; 
v_ext_1465_ = lean_ctor_get(v_attr_1428_, 1);
v_toEnvExtension_1466_ = lean_ctor_get(v_ext_1465_, 0);
v_attr_1467_ = lean_ctor_get(v_attr_1428_, 0);
v_asyncMode_1468_ = lean_ctor_get(v_toEnvExtension_1466_, 2);
lean_inc(v_decl_1429_);
lean_inc_ref(v_env_1461_);
v___x_1469_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1461_, v_decl_1429_, v_asyncMode_1468_);
if (v___x_1469_ == 0)
{
lean_object* v_toAttributeImplCore_1470_; lean_object* v_name_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v_attr_1467_);
lean_dec_ref(v_attr_1428_);
v_toAttributeImplCore_1470_ = lean_ctor_get(v_attr_1467_, 0);
lean_inc_ref(v_toAttributeImplCore_1470_);
lean_dec_ref(v_attr_1467_);
v_name_1471_ = lean_ctor_get(v_toAttributeImplCore_1470_, 1);
lean_inc(v_name_1471_);
lean_dec_ref(v_toAttributeImplCore_1470_);
v___x_1472_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1461_);
v___x_1473_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_1471_, v_decl_1429_, v___x_1472_, v___y_1463_, v___y_1464_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_env_1461_);
v___y_1434_ = v___y_1464_;
goto v___jp_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object* v_attr_1479_, lean_object* v_decl_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1479_, v_decl_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object* v_declName_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
lean_inc(v_declName_1485_);
v___x_1489_ = l_Lean_validateDefEqAttr(v_declName_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref_known(v___x_1489_, 1);
v___x_1490_ = l_Lean_backwardDefeqAttr;
v___x_1491_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v___x_1490_, v_declName_1485_, v___y_1486_, v___y_1487_);
return v___x_1491_;
}
else
{
lean_dec(v_declName_1485_);
return v___x_1489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_declName_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___f_1507_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1508_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1509_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1510_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1511_ = 0;
v___x_1512_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1513_ = l_Lean_registerTagAttribute(v___x_1508_, v___x_1509_, v___f_1507_, v___x_1510_, v___x_1511_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1516_, lean_object* v_attrName_1517_, lean_object* v_declName_1518_, lean_object* v_asyncPrefix_x3f_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1517_, v_declName_1518_, v_asyncPrefix_x3f_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_attrName_1525_, lean_object* v_declName_1526_, lean_object* v_asyncPrefix_x3f_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1524_, v_attrName_1525_, v_declName_1526_, v_asyncPrefix_x3f_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_1532_, lean_object* v_attrName_1533_, lean_object* v_declName_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1533_, v_declName_1534_, v___y_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_1539_, lean_object* v_attrName_1540_, lean_object* v_declName_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_1539_, v_attrName_1540_, v_declName_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1549_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0));
v___x_1550_ = l_Lean_addBuiltinDocString(v___x_1548_, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1580_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6));
v___x_1581_ = l_Lean_addBuiltinDeclarationRanges(v___x_1579_, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* v_type_1595_, lean_object* v_proof_1596_, lean_object* v_a_1597_){
_start:
{
if (lean_obj_tag(v_type_1595_) == 7)
{
if (lean_obj_tag(v_proof_1596_) == 6)
{
lean_object* v_body_1599_; lean_object* v_body_1600_; 
v_body_1599_ = lean_ctor_get(v_type_1595_, 2);
v_body_1600_ = lean_ctor_get(v_proof_1596_, 2);
lean_inc_ref(v_body_1600_);
lean_dec_ref_known(v_proof_1596_, 3);
v_type_1595_ = v_body_1599_;
v_proof_1596_ = v_body_1600_;
goto _start;
}
else
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v_proof_1596_);
v___x_1602_ = 0;
v___x_1603_ = lean_box(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_1606_ = lean_unsigned_to_nat(3u);
v___x_1607_ = l_Lean_Expr_isAppOfArity(v_type_1595_, v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_proof_1596_);
v___x_1608_ = lean_box(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1));
v___x_1611_ = lean_unsigned_to_nat(2u);
v___x_1612_ = l_Lean_Expr_isAppOfArity(v_proof_1596_, v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3));
v___x_1614_ = l_Lean_Expr_isAppOfArity(v_proof_1596_, v___x_1613_, v___x_1611_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5));
v___x_1616_ = lean_unsigned_to_nat(4u);
v___x_1617_ = l_Lean_Expr_isAppOfArity(v_proof_1596_, v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = l_Lean_Expr_getAppFn(v_proof_1596_);
lean_dec_ref(v_proof_1596_);
v___x_1619_ = l_Lean_Expr_isConst(v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec_ref(v___x_1618_);
v___x_1620_ = lean_box(v___x_1619_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v_env_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1622_ = lean_st_ref_get(v_a_1597_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref_n(v_env_1623_, 2);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_Expr_constName_x21(v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1625_ = l_Lean_defeqAttr;
lean_inc(v___x_1624_);
v___x_1626_ = l_Lean_TagAttribute_hasTag(v___x_1625_, v_env_1623_, v___x_1624_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1627_ = l_Lean_backwardDefeqAttr;
v___x_1628_ = l_Lean_TagAttribute_hasTag(v___x_1627_, v_env_1623_, v___x_1624_);
v___x_1629_ = lean_box(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v___x_1624_);
lean_dec_ref(v_env_1623_);
v___x_1631_ = lean_box(v___x_1607_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_appArg_x21(v_proof_1596_);
lean_dec_ref(v_proof_1596_);
v_proof_1596_ = v___x_1633_;
goto _start;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_proof_1596_);
v___x_1635_ = lean_box(v___x_1607_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_proof_1596_);
v___x_1637_ = lean_box(v___x_1607_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* v_type_1639_, lean_object* v_proof_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1639_, v_proof_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_type_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* v_type_1644_, lean_object* v_proof_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1644_, v_proof_1645_, v_a_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* v_type_1650_, lean_object* v_proof_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1650_, v_proof_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_type_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object* v_attrName_1656_, lean_object* v_declName_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1663_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1664_ = l_Lean_MessageData_ofName(v_attrName_1656_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = 0;
v___x_1669_ = l_Lean_MessageData_ofConstName(v_declName_1657_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1667_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1672_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1674_, lean_object* v_declName_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1674_, v_declName_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object* v_attrName_1682_, lean_object* v_declName_1683_, lean_object* v_asyncPrefix_x3f_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___y_1691_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1684_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_MessageData_nil;
v___y_1691_ = v___x_1704_;
goto v___jp_1690_;
}
else
{
lean_object* v_val_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_val_1705_ = lean_ctor_get(v_asyncPrefix_x3f_1684_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v_asyncPrefix_x3f_1684_, 1);
v___x_1706_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1707_ = l_Lean_MessageData_ofName(v_val_1705_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___y_1691_ = v___x_1710_;
goto v___jp_1690_;
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1692_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1693_ = l_Lean_MessageData_ofName(v_attrName_1682_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = 0;
v___x_1698_ = l_Lean_MessageData_ofConstName(v_declName_1683_, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___y_1691_);
v___x_1703_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1702_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1711_, lean_object* v_declName_1712_, lean_object* v_asyncPrefix_x3f_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1711_, v_declName_1712_, v_asyncPrefix_x3f_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object* v_attr_1720_, lean_object* v_decl_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___x_1770_; lean_object* v_env_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___x_1786_; 
v___x_1770_ = lean_st_ref_get(v___y_1725_);
v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc_ref(v_env_1771_);
lean_dec(v___x_1770_);
v___x_1786_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1771_, v_decl_1721_);
if (lean_obj_tag(v___x_1786_) == 0)
{
v___y_1773_ = v___y_1722_;
v___y_1774_ = v___y_1723_;
v___y_1775_ = v___y_1724_;
v___y_1776_ = v___y_1725_;
goto v___jp_1772_;
}
else
{
lean_object* v_attr_1787_; lean_object* v_toAttributeImplCore_1788_; lean_object* v_name_1789_; lean_object* v___x_1790_; 
lean_dec_ref_known(v___x_1786_, 1);
lean_dec_ref(v_env_1771_);
v_attr_1787_ = lean_ctor_get(v_attr_1720_, 0);
lean_inc_ref(v_attr_1787_);
lean_dec_ref(v_attr_1720_);
v_toAttributeImplCore_1788_ = lean_ctor_get(v_attr_1787_, 0);
lean_inc_ref(v_toAttributeImplCore_1788_);
lean_dec_ref(v_attr_1787_);
v_name_1789_ = lean_ctor_get(v_toAttributeImplCore_1788_, 1);
lean_inc(v_name_1789_);
lean_dec_ref(v_toAttributeImplCore_1788_);
v___x_1790_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_1789_, v_decl_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1790_;
}
v___jp_1727_:
{
lean_object* v___x_1730_; lean_object* v_ext_1731_; lean_object* v_toEnvExtension_1732_; lean_object* v_env_1733_; lean_object* v_nextMacroScope_1734_; lean_object* v_ngen_1735_; lean_object* v_auxDeclNGen_1736_; lean_object* v_traceState_1737_; lean_object* v_messages_1738_; lean_object* v_infoState_1739_; lean_object* v_snapshotTasks_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1768_; 
v___x_1730_ = lean_st_ref_take(v___y_1729_);
v_ext_1731_ = lean_ctor_get(v_attr_1720_, 1);
lean_inc_ref(v_ext_1731_);
lean_dec_ref(v_attr_1720_);
v_toEnvExtension_1732_ = lean_ctor_get(v_ext_1731_, 0);
v_env_1733_ = lean_ctor_get(v___x_1730_, 0);
v_nextMacroScope_1734_ = lean_ctor_get(v___x_1730_, 1);
v_ngen_1735_ = lean_ctor_get(v___x_1730_, 2);
v_auxDeclNGen_1736_ = lean_ctor_get(v___x_1730_, 3);
v_traceState_1737_ = lean_ctor_get(v___x_1730_, 4);
v_messages_1738_ = lean_ctor_get(v___x_1730_, 6);
v_infoState_1739_ = lean_ctor_get(v___x_1730_, 7);
v_snapshotTasks_1740_ = lean_ctor_get(v___x_1730_, 8);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1730_, 5);
lean_dec(v_unused_1769_);
v___x_1742_ = v___x_1730_;
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snapshotTasks_1740_);
lean_inc(v_infoState_1739_);
lean_inc(v_messages_1738_);
lean_inc(v_traceState_1737_);
lean_inc(v_auxDeclNGen_1736_);
lean_inc(v_ngen_1735_);
lean_inc(v_nextMacroScope_1734_);
lean_inc(v_env_1733_);
lean_dec(v___x_1730_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_asyncMode_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v_asyncMode_1744_ = lean_ctor_get(v_toEnvExtension_1732_, 2);
lean_inc(v_asyncMode_1744_);
lean_inc(v_decl_1721_);
v___x_1745_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1731_, v_env_1733_, v_decl_1721_, v_asyncMode_1744_, v_decl_1721_);
lean_dec(v_asyncMode_1744_);
v___x_1746_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 5, v___x_1746_);
lean_ctor_set(v___x_1742_, 0, v___x_1745_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_nextMacroScope_1734_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_ngen_1735_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_auxDeclNGen_1736_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_traceState_1737_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1767_, 6, v_messages_1738_);
lean_ctor_set(v_reuseFailAlloc_1767_, 7, v_infoState_1739_);
lean_ctor_set(v_reuseFailAlloc_1767_, 8, v_snapshotTasks_1740_);
v___x_1748_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_mctx_1751_; lean_object* v_zetaDeltaFVarIds_1752_; lean_object* v_postponed_1753_; lean_object* v_diag_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1765_; 
v___x_1749_ = lean_st_ref_set(v___y_1729_, v___x_1748_);
v___x_1750_ = lean_st_ref_take(v___y_1728_);
v_mctx_1751_ = lean_ctor_get(v___x_1750_, 0);
v_zetaDeltaFVarIds_1752_ = lean_ctor_get(v___x_1750_, 2);
v_postponed_1753_ = lean_ctor_get(v___x_1750_, 3);
v_diag_1754_ = lean_ctor_get(v___x_1750_, 4);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1750_, 1);
lean_dec(v_unused_1766_);
v___x_1756_ = v___x_1750_;
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_diag_1754_);
lean_inc(v_postponed_1753_);
lean_inc(v_zetaDeltaFVarIds_1752_);
lean_inc(v_mctx_1751_);
lean_dec(v___x_1750_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_mctx_1751_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_zetaDeltaFVarIds_1752_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_postponed_1753_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_diag_1754_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_st_ref_set(v___y_1728_, v___x_1760_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
}
v___jp_1772_:
{
lean_object* v_ext_1777_; lean_object* v_toEnvExtension_1778_; lean_object* v_attr_1779_; lean_object* v_asyncMode_1780_; uint8_t v___x_1781_; 
v_ext_1777_ = lean_ctor_get(v_attr_1720_, 1);
v_toEnvExtension_1778_ = lean_ctor_get(v_ext_1777_, 0);
v_attr_1779_ = lean_ctor_get(v_attr_1720_, 0);
v_asyncMode_1780_ = lean_ctor_get(v_toEnvExtension_1778_, 2);
lean_inc(v_decl_1721_);
lean_inc_ref(v_env_1771_);
v___x_1781_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1771_, v_decl_1721_, v_asyncMode_1780_);
if (v___x_1781_ == 0)
{
lean_object* v_toAttributeImplCore_1782_; lean_object* v_name_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_inc_ref(v_attr_1779_);
lean_dec_ref(v_attr_1720_);
v_toAttributeImplCore_1782_ = lean_ctor_get(v_attr_1779_, 0);
lean_inc_ref(v_toAttributeImplCore_1782_);
lean_dec_ref(v_attr_1779_);
v_name_1783_ = lean_ctor_get(v_toAttributeImplCore_1782_, 1);
lean_inc(v_name_1783_);
lean_dec_ref(v_toAttributeImplCore_1782_);
v___x_1784_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1771_);
v___x_1785_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_1783_, v_decl_1721_, v___x_1784_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1785_;
}
else
{
lean_dec_ref(v_env_1771_);
v___y_1728_ = v___y_1774_;
v___y_1729_ = v___y_1776_;
goto v___jp_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object* v_attr_1791_, lean_object* v_decl_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_1791_, v_decl_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1799_, lean_object* v_declHint_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_env_1804_; uint8_t v___y_1806_; uint8_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1803_ = lean_st_ref_get(v___y_1801_);
v_env_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_ref(v_env_1804_);
lean_dec(v___x_1803_);
v___x_1864_ = l_Lean_Name_isAnonymous(v_declHint_1800_);
v___x_1865_ = lean_bool_not(v___x_1864_);
if (v___x_1865_ == 0)
{
v___y_1806_ = v___x_1865_;
goto v___jp_1805_;
}
else
{
uint8_t v_isExporting_1866_; 
v_isExporting_1866_ = lean_ctor_get_uint8(v_env_1804_, sizeof(void*)*8);
v___y_1806_ = v_isExporting_1866_;
goto v___jp_1805_;
}
v___jp_1805_:
{
if (v___y_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1799_);
return v___x_1807_;
}
else
{
uint8_t v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = 0;
lean_inc_ref(v_env_1804_);
v___x_1809_ = l_Lean_Environment_setExporting(v_env_1804_, v___x_1808_);
lean_inc(v_declHint_1800_);
lean_inc_ref(v___x_1809_);
v___x_1810_ = l_Lean_Environment_contains(v___x_1809_, v_declHint_1800_, v___y_1806_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_msg_1799_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_c_1819_; lean_object* v___x_1820_; 
v___x_1812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1813_ = lean_unsigned_to_nat(32u);
v___x_1814_ = lean_mk_empty_array_with_capacity(v___x_1813_);
lean_dec_ref(v___x_1814_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1816_ = l_Lean_Options_empty;
v___x_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1809_);
lean_ctor_set(v___x_1817_, 1, v___x_1812_);
lean_ctor_set(v___x_1817_, 2, v___x_1815_);
lean_ctor_set(v___x_1817_, 3, v___x_1816_);
lean_inc(v_declHint_1800_);
v___x_1818_ = l_Lean_MessageData_ofConstName(v_declHint_1800_, v___x_1808_);
v_c_1819_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1819_, 0, v___x_1817_);
lean_ctor_set(v_c_1819_, 1, v___x_1818_);
v___x_1820_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1804_, v_declHint_1800_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_c_1819_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_MessageData_note(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_msg_1799_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
else
{
lean_object* v_val_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1863_; 
v_val_1828_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1830_ = v___x_1820_;
v_isShared_1831_ = v_isSharedCheck_1863_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_val_1828_);
lean_dec(v___x_1820_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1863_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_mod_1835_; uint8_t v___x_1836_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Environment_header(v_env_1804_);
lean_dec_ref(v_env_1804_);
v___x_1834_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1833_);
v_mod_1835_ = lean_array_get(v___x_1832_, v___x_1834_, v_val_1828_);
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = l_Lean_isPrivateName(v_declHint_1800_);
lean_dec(v_declHint_1800_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v_c_1819_);
v___x_1839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_MessageData_ofName(v_mod_1835_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_MessageData_note(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_msg_1799_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1846_);
v___x_1848_ = v___x_1830_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_c_1819_);
v___x_1852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_MessageData_ofName(v_mod_1835_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Lean_MessageData_note(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_msg_1799_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1859_);
v___x_1861_ = v___x_1830_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1867_, lean_object* v_declHint_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1867_, v_declHint_1868_, v___y_1869_);
lean_dec(v___y_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object* v_msg_1872_, lean_object* v_declHint_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v___x_1879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1872_, v_declHint_1873_, v___y_1877_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1884_ = l_Lean_unknownIdentifierMessageTag;
v___x_1885_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v_a_1880_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1885_);
v___x_1887_ = v___x_1882_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object* v_msg_1890_, lean_object* v_declHint_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1890_, v_declHint_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_fileName_1905_; lean_object* v_fileMap_1906_; lean_object* v_options_1907_; lean_object* v_currRecDepth_1908_; lean_object* v_maxRecDepth_1909_; lean_object* v_ref_1910_; lean_object* v_currNamespace_1911_; lean_object* v_openDecls_1912_; lean_object* v_initHeartbeats_1913_; lean_object* v_maxHeartbeats_1914_; lean_object* v_quotContext_1915_; lean_object* v_currMacroScope_1916_; uint8_t v_diag_1917_; lean_object* v_cancelTk_x3f_1918_; uint8_t v_suppressElabErrors_1919_; lean_object* v_inheritedTraceOptions_1920_; lean_object* v_ref_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_fileName_1905_ = lean_ctor_get(v___y_1902_, 0);
v_fileMap_1906_ = lean_ctor_get(v___y_1902_, 1);
v_options_1907_ = lean_ctor_get(v___y_1902_, 2);
v_currRecDepth_1908_ = lean_ctor_get(v___y_1902_, 3);
v_maxRecDepth_1909_ = lean_ctor_get(v___y_1902_, 4);
v_ref_1910_ = lean_ctor_get(v___y_1902_, 5);
v_currNamespace_1911_ = lean_ctor_get(v___y_1902_, 6);
v_openDecls_1912_ = lean_ctor_get(v___y_1902_, 7);
v_initHeartbeats_1913_ = lean_ctor_get(v___y_1902_, 8);
v_maxHeartbeats_1914_ = lean_ctor_get(v___y_1902_, 9);
v_quotContext_1915_ = lean_ctor_get(v___y_1902_, 10);
v_currMacroScope_1916_ = lean_ctor_get(v___y_1902_, 11);
v_diag_1917_ = lean_ctor_get_uint8(v___y_1902_, sizeof(void*)*14);
v_cancelTk_x3f_1918_ = lean_ctor_get(v___y_1902_, 12);
v_suppressElabErrors_1919_ = lean_ctor_get_uint8(v___y_1902_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1920_ = lean_ctor_get(v___y_1902_, 13);
v_ref_1921_ = l_Lean_replaceRef(v_ref_1898_, v_ref_1910_);
lean_inc_ref(v_inheritedTraceOptions_1920_);
lean_inc(v_cancelTk_x3f_1918_);
lean_inc(v_currMacroScope_1916_);
lean_inc(v_quotContext_1915_);
lean_inc(v_maxHeartbeats_1914_);
lean_inc(v_initHeartbeats_1913_);
lean_inc(v_openDecls_1912_);
lean_inc(v_currNamespace_1911_);
lean_inc(v_maxRecDepth_1909_);
lean_inc(v_currRecDepth_1908_);
lean_inc_ref(v_options_1907_);
lean_inc_ref(v_fileMap_1906_);
lean_inc_ref(v_fileName_1905_);
v___x_1922_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1922_, 0, v_fileName_1905_);
lean_ctor_set(v___x_1922_, 1, v_fileMap_1906_);
lean_ctor_set(v___x_1922_, 2, v_options_1907_);
lean_ctor_set(v___x_1922_, 3, v_currRecDepth_1908_);
lean_ctor_set(v___x_1922_, 4, v_maxRecDepth_1909_);
lean_ctor_set(v___x_1922_, 5, v_ref_1921_);
lean_ctor_set(v___x_1922_, 6, v_currNamespace_1911_);
lean_ctor_set(v___x_1922_, 7, v_openDecls_1912_);
lean_ctor_set(v___x_1922_, 8, v_initHeartbeats_1913_);
lean_ctor_set(v___x_1922_, 9, v_maxHeartbeats_1914_);
lean_ctor_set(v___x_1922_, 10, v_quotContext_1915_);
lean_ctor_set(v___x_1922_, 11, v_currMacroScope_1916_);
lean_ctor_set(v___x_1922_, 12, v_cancelTk_x3f_1918_);
lean_ctor_set(v___x_1922_, 13, v_inheritedTraceOptions_1920_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*14, v_diag_1917_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*14 + 1, v_suppressElabErrors_1919_);
v___x_1923_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_1899_, v___y_1900_, v___y_1901_, v___x_1922_, v___y_1903_);
lean_dec_ref_known(v___x_1922_, 14);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1924_, v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v_ref_1924_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v_declHint_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1933_, v_declHint_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v___x_1940_);
v___x_1942_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1932_, v_a_1941_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1943_, lean_object* v_msg_1944_, lean_object* v_declHint_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1943_, v_msg_1944_, v_declHint_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v_ref_1943_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object* v_ref_1952_, lean_object* v_constName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1959_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1960_ = 0;
lean_inc(v_constName_1953_);
v___x_1961_ = l_Lean_MessageData_ofConstName(v_constName_1953_, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1952_, v___x_1964_, v_constName_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object* v_ref_1966_, lean_object* v_constName_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1966_, v_constName_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_ref_1966_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object* v_constName_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_ref_1980_; lean_object* v___x_1981_; 
v_ref_1980_ = lean_ctor_get(v___y_1977_, 5);
v___x_1981_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1980_, v_constName_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object* v_constName_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; lean_object* v_env_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_st_ref_get(v___y_1993_);
v_env_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_env_1996_);
lean_dec(v___x_1995_);
v___x_1997_ = 0;
lean_inc(v_constName_1989_);
v___x_1998_ = l_Lean_Environment_find_x3f(v_env_1996_, v_constName_1989_, v___x_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_1999_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_constName_1989_);
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 0);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_val_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object* v_constName_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t v___y_2022_, uint8_t v_suppressElabErrors_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 1)
{
lean_object* v_pre_2025_; 
v_pre_2025_ = lean_ctor_get(v_x_2024_, 0);
switch(lean_obj_tag(v_pre_2025_))
{
case 1:
{
lean_object* v_pre_2026_; 
v_pre_2026_ = lean_ctor_get(v_pre_2025_, 0);
switch(lean_obj_tag(v_pre_2026_))
{
case 0:
{
lean_object* v_str_2027_; lean_object* v_str_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_str_2027_ = lean_ctor_get(v_x_2024_, 1);
v_str_2028_ = lean_ctor_get(v_pre_2025_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0));
v___x_2030_ = lean_string_dec_eq(v_str_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1));
v___x_2032_ = lean_string_dec_eq(v_str_2028_, v___x_2031_);
if (v___x_2032_ == 0)
{
return v___y_2022_;
}
else
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2));
v___x_2034_ = lean_string_dec_eq(v_str_2027_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___y_2022_;
}
else
{
return v_suppressElabErrors_2023_;
}
}
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3));
v___x_2036_ = lean_string_dec_eq(v_str_2027_, v___x_2035_);
if (v___x_2036_ == 0)
{
return v___y_2022_;
}
else
{
return v_suppressElabErrors_2023_;
}
}
}
case 1:
{
lean_object* v_pre_2037_; 
v_pre_2037_ = lean_ctor_get(v_pre_2026_, 0);
if (lean_obj_tag(v_pre_2037_) == 0)
{
lean_object* v_str_2038_; lean_object* v_str_2039_; lean_object* v_str_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_str_2038_ = lean_ctor_get(v_x_2024_, 1);
v_str_2039_ = lean_ctor_get(v_pre_2025_, 1);
v_str_2040_ = lean_ctor_get(v_pre_2026_, 1);
v___x_2041_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4));
v___x_2042_ = lean_string_dec_eq(v_str_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
return v___y_2022_;
}
else
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5));
v___x_2044_ = lean_string_dec_eq(v_str_2039_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v___y_2022_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6));
v___x_2046_ = lean_string_dec_eq(v_str_2038_, v___x_2045_);
if (v___x_2046_ == 0)
{
return v___y_2022_;
}
else
{
return v_suppressElabErrors_2023_;
}
}
}
}
else
{
return v___y_2022_;
}
}
default: 
{
return v___y_2022_;
}
}
}
case 0:
{
lean_object* v_str_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_str_2047_ = lean_ctor_get(v_x_2024_, 1);
v___x_2048_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0));
v___x_2049_ = lean_string_dec_eq(v_str_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
return v___y_2022_;
}
else
{
return v_suppressElabErrors_2023_;
}
}
default: 
{
return v___y_2022_;
}
}
}
else
{
return v___y_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object* v___y_2050_, lean_object* v_suppressElabErrors_2051_, lean_object* v_x_2052_){
_start:
{
uint8_t v___y_8755__boxed_2053_; uint8_t v_suppressElabErrors_boxed_2054_; uint8_t v_res_2055_; lean_object* v_r_2056_; 
v___y_8755__boxed_2053_ = lean_unbox(v___y_2050_);
v_suppressElabErrors_boxed_2054_ = lean_unbox(v_suppressElabErrors_2051_);
v_res_2055_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v___y_8755__boxed_2053_, v_suppressElabErrors_boxed_2054_, v_x_2052_);
lean_dec(v_x_2052_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object* v_ref_2058_, lean_object* v_msgData_2059_, uint8_t v_severity_2060_, uint8_t v_isSilent_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; uint8_t v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2109_; uint8_t v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; uint8_t v___y_2134_; uint8_t v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; uint8_t v___y_2144_; uint8_t v___y_2145_; uint8_t v___y_2146_; uint8_t v___x_2151_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; uint8_t v___y_2156_; lean_object* v___y_2157_; uint8_t v___y_2158_; uint8_t v___y_2159_; uint8_t v___y_2161_; uint8_t v___x_2176_; 
v___x_2151_ = 2;
v___x_2176_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2060_, v___x_2151_);
if (v___x_2176_ == 0)
{
v___y_2161_ = v___x_2176_;
goto v___jp_2160_;
}
else
{
uint8_t v___x_2177_; 
lean_inc_ref(v_msgData_2059_);
v___x_2177_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2059_);
v___y_2161_ = v___x_2177_;
goto v___jp_2160_;
}
v___jp_2067_:
{
lean_object* v___x_2077_; lean_object* v_currNamespace_2078_; lean_object* v_openDecls_2079_; lean_object* v_env_2080_; lean_object* v_nextMacroScope_2081_; lean_object* v_ngen_2082_; lean_object* v_auxDeclNGen_2083_; lean_object* v_traceState_2084_; lean_object* v_cache_2085_; lean_object* v_messages_2086_; lean_object* v_infoState_2087_; lean_object* v_snapshotTasks_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2102_; 
v___x_2077_ = lean_st_ref_take(v___y_2076_);
v_currNamespace_2078_ = lean_ctor_get(v___y_2075_, 6);
v_openDecls_2079_ = lean_ctor_get(v___y_2075_, 7);
v_env_2080_ = lean_ctor_get(v___x_2077_, 0);
v_nextMacroScope_2081_ = lean_ctor_get(v___x_2077_, 1);
v_ngen_2082_ = lean_ctor_get(v___x_2077_, 2);
v_auxDeclNGen_2083_ = lean_ctor_get(v___x_2077_, 3);
v_traceState_2084_ = lean_ctor_get(v___x_2077_, 4);
v_cache_2085_ = lean_ctor_get(v___x_2077_, 5);
v_messages_2086_ = lean_ctor_get(v___x_2077_, 6);
v_infoState_2087_ = lean_ctor_get(v___x_2077_, 7);
v_snapshotTasks_2088_ = lean_ctor_get(v___x_2077_, 8);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2090_ = v___x_2077_;
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_snapshotTasks_2088_);
lean_inc(v_infoState_2087_);
lean_inc(v_messages_2086_);
lean_inc(v_cache_2085_);
lean_inc(v_traceState_2084_);
lean_inc(v_auxDeclNGen_2083_);
lean_inc(v_ngen_2082_);
lean_inc(v_nextMacroScope_2081_);
lean_inc(v_env_2080_);
lean_dec(v___x_2077_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc(v_openDecls_2079_);
lean_inc(v_currNamespace_2078_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v_currNamespace_2078_);
lean_ctor_set(v___x_2092_, 1, v_openDecls_2079_);
v___x_2093_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___y_2072_);
lean_inc_ref(v___y_2070_);
lean_inc_ref(v___y_2068_);
v___x_2094_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2094_, 0, v___y_2068_);
lean_ctor_set(v___x_2094_, 1, v___y_2074_);
lean_ctor_set(v___x_2094_, 2, v___y_2071_);
lean_ctor_set(v___x_2094_, 3, v___y_2070_);
lean_ctor_set(v___x_2094_, 4, v___x_2093_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*5, v___y_2073_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*5 + 1, v___y_2069_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*5 + 2, v_isSilent_2061_);
v___x_2095_ = l_Lean_MessageLog_add(v___x_2094_, v_messages_2086_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 6, v___x_2095_);
v___x_2097_ = v___x_2090_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_env_2080_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_nextMacroScope_2081_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_ngen_2082_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v_auxDeclNGen_2083_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_traceState_2084_);
lean_ctor_set(v_reuseFailAlloc_2101_, 5, v_cache_2085_);
lean_ctor_set(v_reuseFailAlloc_2101_, 6, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2101_, 7, v_infoState_2087_);
lean_ctor_set(v_reuseFailAlloc_2101_, 8, v_snapshotTasks_2088_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_st_ref_set(v___y_2076_, v___x_2097_);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
v___jp_2103_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2127_; 
v___x_2112_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2059_);
v___x_2113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_2112_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_inc_ref_n(v___y_2106_, 2);
v___x_2118_ = l_Lean_FileMap_toPosition(v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
v___x_2119_ = l_Lean_FileMap_toPosition(v___y_2106_, v___y_2111_);
lean_dec(v___y_2111_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
v___x_2121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0));
if (v___y_2109_ == 0)
{
lean_del_object(v___x_2116_);
lean_dec_ref(v___y_2104_);
v___y_2068_ = v___y_2105_;
v___y_2069_ = v___y_2108_;
v___y_2070_ = v___x_2121_;
v___y_2071_ = v___x_2120_;
v___y_2072_ = v_a_2114_;
v___y_2073_ = v___y_2110_;
v___y_2074_ = v___x_2118_;
v___y_2075_ = v___y_2064_;
v___y_2076_ = v___y_2065_;
goto v___jp_2067_;
}
else
{
uint8_t v___x_2122_; 
lean_inc(v_a_2114_);
v___x_2122_ = l_Lean_MessageData_hasTag(v___y_2104_, v_a_2114_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec_ref_known(v___x_2120_, 1);
lean_dec_ref(v___x_2118_);
lean_dec(v_a_2114_);
v___x_2123_ = lean_box(0);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2123_);
v___x_2125_ = v___x_2116_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_del_object(v___x_2116_);
v___y_2068_ = v___y_2105_;
v___y_2069_ = v___y_2108_;
v___y_2070_ = v___x_2121_;
v___y_2071_ = v___x_2120_;
v___y_2072_ = v_a_2114_;
v___y_2073_ = v___y_2110_;
v___y_2074_ = v___x_2118_;
v___y_2075_ = v___y_2064_;
v___y_2076_ = v___y_2065_;
goto v___jp_2067_;
}
}
}
}
v___jp_2128_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_Syntax_getTailPos_x3f(v___y_2132_, v___y_2135_);
lean_dec(v___y_2132_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_inc(v___y_2136_);
v___y_2104_ = v___y_2129_;
v___y_2105_ = v___y_2131_;
v___y_2106_ = v___y_2130_;
v___y_2107_ = v___y_2136_;
v___y_2108_ = v___y_2133_;
v___y_2109_ = v___y_2134_;
v___y_2110_ = v___y_2135_;
v___y_2111_ = v___y_2136_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2138_; 
v_val_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___y_2104_ = v___y_2129_;
v___y_2105_ = v___y_2131_;
v___y_2106_ = v___y_2130_;
v___y_2107_ = v___y_2136_;
v___y_2108_ = v___y_2133_;
v___y_2109_ = v___y_2134_;
v___y_2110_ = v___y_2135_;
v___y_2111_ = v_val_2138_;
goto v___jp_2103_;
}
}
v___jp_2139_:
{
lean_object* v_ref_2147_; lean_object* v___x_2148_; 
v_ref_2147_ = l_Lean_replaceRef(v_ref_2058_, v___y_2143_);
v___x_2148_ = l_Lean_Syntax_getPos_x3f(v_ref_2147_, v___y_2145_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___y_2129_ = v___y_2140_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v___y_2141_;
v___y_2132_ = v_ref_2147_;
v___y_2133_ = v___y_2146_;
v___y_2134_ = v___y_2144_;
v___y_2135_ = v___y_2145_;
v___y_2136_ = v___x_2149_;
goto v___jp_2128_;
}
else
{
lean_object* v_val_2150_; 
v_val_2150_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2148_, 1);
v___y_2129_ = v___y_2140_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v___y_2141_;
v___y_2132_ = v_ref_2147_;
v___y_2133_ = v___y_2146_;
v___y_2134_ = v___y_2144_;
v___y_2135_ = v___y_2145_;
v___y_2136_ = v_val_2150_;
goto v___jp_2128_;
}
}
v___jp_2152_:
{
if (v___y_2159_ == 0)
{
v___y_2140_ = v___y_2157_;
v___y_2141_ = v___y_2154_;
v___y_2142_ = v___y_2153_;
v___y_2143_ = v___y_2155_;
v___y_2144_ = v___y_2156_;
v___y_2145_ = v___y_2158_;
v___y_2146_ = v_severity_2060_;
goto v___jp_2139_;
}
else
{
v___y_2140_ = v___y_2157_;
v___y_2141_ = v___y_2154_;
v___y_2142_ = v___y_2153_;
v___y_2143_ = v___y_2155_;
v___y_2144_ = v___y_2156_;
v___y_2145_ = v___y_2158_;
v___y_2146_ = v___x_2151_;
goto v___jp_2139_;
}
}
v___jp_2160_:
{
if (v___y_2161_ == 0)
{
lean_object* v_fileName_2162_; lean_object* v_fileMap_2163_; lean_object* v_options_2164_; lean_object* v_ref_2165_; uint8_t v_suppressElabErrors_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; uint8_t v___x_2170_; uint8_t v___x_2171_; 
v_fileName_2162_ = lean_ctor_get(v___y_2064_, 0);
v_fileMap_2163_ = lean_ctor_get(v___y_2064_, 1);
v_options_2164_ = lean_ctor_get(v___y_2064_, 2);
v_ref_2165_ = lean_ctor_get(v___y_2064_, 5);
v_suppressElabErrors_2166_ = lean_ctor_get_uint8(v___y_2064_, sizeof(void*)*14 + 1);
v___x_2167_ = lean_box(v___y_2161_);
v___x_2168_ = lean_box(v_suppressElabErrors_2166_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2169_, 0, v___x_2167_);
lean_closure_set(v___f_2169_, 1, v___x_2168_);
v___x_2170_ = 1;
v___x_2171_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2060_, v___x_2170_);
if (v___x_2171_ == 0)
{
v___y_2153_ = v_fileMap_2163_;
v___y_2154_ = v_fileName_2162_;
v___y_2155_ = v_ref_2165_;
v___y_2156_ = v_suppressElabErrors_2166_;
v___y_2157_ = v___f_2169_;
v___y_2158_ = v___y_2161_;
v___y_2159_ = v___x_2171_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = l_Lean_warningAsError;
v___x_2173_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_2164_, v___x_2172_);
v___y_2153_ = v_fileMap_2163_;
v___y_2154_ = v_fileName_2162_;
v___y_2155_ = v_ref_2165_;
v___y_2156_ = v_suppressElabErrors_2166_;
v___y_2157_ = v___f_2169_;
v___y_2158_ = v___y_2161_;
v___y_2159_ = v___x_2173_;
goto v___jp_2152_;
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_msgData_2059_);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object* v_ref_2178_, lean_object* v_msgData_2179_, lean_object* v_severity_2180_, lean_object* v_isSilent_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v_severity_boxed_2187_; uint8_t v_isSilent_boxed_2188_; lean_object* v_res_2189_; 
v_severity_boxed_2187_ = lean_unbox(v_severity_2180_);
v_isSilent_boxed_2188_ = lean_unbox(v_isSilent_2181_);
v_res_2189_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2178_, v_msgData_2179_, v_severity_boxed_2187_, v_isSilent_boxed_2188_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v_ref_2178_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object* v_msgData_2190_, uint8_t v_severity_2191_, uint8_t v_isSilent_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_ref_2198_; lean_object* v___x_2199_; 
v_ref_2198_ = lean_ctor_get(v___y_2195_, 5);
v___x_2199_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2198_, v_msgData_2190_, v_severity_2191_, v_isSilent_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object* v_msgData_2200_, lean_object* v_severity_2201_, lean_object* v_isSilent_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v_severity_boxed_2208_; uint8_t v_isSilent_boxed_2209_; lean_object* v_res_2210_; 
v_severity_boxed_2208_ = lean_unbox(v_severity_2201_);
v_isSilent_boxed_2209_ = lean_unbox(v_isSilent_2202_);
v_res_2210_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2200_, v_severity_boxed_2208_, v_isSilent_boxed_2209_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object* v_msgData_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = 2;
v___x_2218_ = 0;
v___x_2219_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2211_, v___x_2217_, v___x_2218_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object* v_msgData_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object* v___y_2227_, uint8_t v_isExporting_2228_, lean_object* v___x_2229_, lean_object* v___y_2230_, lean_object* v___x_2231_, lean_object* v_a_x3f_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v_env_2235_; lean_object* v_nextMacroScope_2236_; lean_object* v_ngen_2237_; lean_object* v_auxDeclNGen_2238_; lean_object* v_traceState_2239_; lean_object* v_messages_2240_; lean_object* v_infoState_2241_; lean_object* v_snapshotTasks_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2267_; 
v___x_2234_ = lean_st_ref_take(v___y_2227_);
v_env_2235_ = lean_ctor_get(v___x_2234_, 0);
v_nextMacroScope_2236_ = lean_ctor_get(v___x_2234_, 1);
v_ngen_2237_ = lean_ctor_get(v___x_2234_, 2);
v_auxDeclNGen_2238_ = lean_ctor_get(v___x_2234_, 3);
v_traceState_2239_ = lean_ctor_get(v___x_2234_, 4);
v_messages_2240_ = lean_ctor_get(v___x_2234_, 6);
v_infoState_2241_ = lean_ctor_get(v___x_2234_, 7);
v_snapshotTasks_2242_ = lean_ctor_get(v___x_2234_, 8);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v___x_2234_, 5);
lean_dec(v_unused_2268_);
v___x_2244_ = v___x_2234_;
v_isShared_2245_ = v_isSharedCheck_2267_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snapshotTasks_2242_);
lean_inc(v_infoState_2241_);
lean_inc(v_messages_2240_);
lean_inc(v_traceState_2239_);
lean_inc(v_auxDeclNGen_2238_);
lean_inc(v_ngen_2237_);
lean_inc(v_nextMacroScope_2236_);
lean_inc(v_env_2235_);
lean_dec(v___x_2234_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2267_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = l_Lean_Environment_setExporting(v_env_2235_, v_isExporting_2228_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 5, v___x_2229_);
lean_ctor_set(v___x_2244_, 0, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_nextMacroScope_2236_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_ngen_2237_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_auxDeclNGen_2238_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_traceState_2239_);
lean_ctor_set(v_reuseFailAlloc_2266_, 5, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2266_, 6, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2266_, 7, v_infoState_2241_);
lean_ctor_set(v_reuseFailAlloc_2266_, 8, v_snapshotTasks_2242_);
v___x_2248_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_mctx_2251_; lean_object* v_zetaDeltaFVarIds_2252_; lean_object* v_postponed_2253_; lean_object* v_diag_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2264_; 
v___x_2249_ = lean_st_ref_set(v___y_2227_, v___x_2248_);
v___x_2250_ = lean_st_ref_take(v___y_2230_);
v_mctx_2251_ = lean_ctor_get(v___x_2250_, 0);
v_zetaDeltaFVarIds_2252_ = lean_ctor_get(v___x_2250_, 2);
v_postponed_2253_ = lean_ctor_get(v___x_2250_, 3);
v_diag_2254_ = lean_ctor_get(v___x_2250_, 4);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2250_, 1);
lean_dec(v_unused_2265_);
v___x_2256_ = v___x_2250_;
v_isShared_2257_ = v_isSharedCheck_2264_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_diag_2254_);
lean_inc(v_postponed_2253_);
lean_inc(v_zetaDeltaFVarIds_2252_);
lean_inc(v_mctx_2251_);
lean_dec(v___x_2250_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2264_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2231_);
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_mctx_2251_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_zetaDeltaFVarIds_2252_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_postponed_2253_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_diag_2254_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_st_ref_set(v___y_2230_, v___x_2259_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object* v___y_2269_, lean_object* v_isExporting_2270_, lean_object* v___x_2271_, lean_object* v___y_2272_, lean_object* v___x_2273_, lean_object* v_a_x3f_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v_isExporting_boxed_2276_; lean_object* v_res_2277_; 
v_isExporting_boxed_2276_ = lean_unbox(v_isExporting_2270_);
v_res_2277_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2269_, v_isExporting_boxed_2276_, v___x_2271_, v___y_2272_, v___x_2273_, v_a_x3f_2274_);
lean_dec(v_a_x3f_2274_);
lean_dec(v___y_2272_);
lean_dec(v___y_2269_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object* v_declName_2278_, uint8_t v_isExporting_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v_env_2285_; uint8_t v_isExporting_2286_; uint8_t v___y_2353_; lean_object* v___x_2355_; uint8_t v_isModule_2356_; uint8_t v___x_2357_; 
v___x_2284_ = lean_st_ref_get(v___y_2282_);
v_env_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_env_2285_);
lean_dec(v___x_2284_);
v_isExporting_2286_ = lean_ctor_get_uint8(v_env_2285_, sizeof(void*)*8);
v___x_2355_ = l_Lean_Environment_header(v_env_2285_);
lean_dec_ref(v_env_2285_);
v_isModule_2356_ = lean_ctor_get_uint8(v___x_2355_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_bool_not(v_isModule_2356_);
if (v___x_2357_ == 0)
{
if (v_isExporting_2286_ == 0)
{
if (v_isExporting_2279_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_validateDefEqAttr(v_declName_2278_, v___y_2281_, v___y_2282_);
return v___x_2358_;
}
else
{
goto v___jp_2287_;
}
}
else
{
v___y_2353_ = v_isExporting_2279_;
goto v___jp_2352_;
}
}
else
{
v___y_2353_ = v___x_2357_;
goto v___jp_2352_;
}
v___jp_2287_:
{
lean_object* v___x_2288_; lean_object* v_env_2289_; lean_object* v_nextMacroScope_2290_; lean_object* v_ngen_2291_; lean_object* v_auxDeclNGen_2292_; lean_object* v_traceState_2293_; lean_object* v_messages_2294_; lean_object* v_infoState_2295_; lean_object* v_snapshotTasks_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2350_; 
v___x_2288_ = lean_st_ref_take(v___y_2282_);
v_env_2289_ = lean_ctor_get(v___x_2288_, 0);
v_nextMacroScope_2290_ = lean_ctor_get(v___x_2288_, 1);
v_ngen_2291_ = lean_ctor_get(v___x_2288_, 2);
v_auxDeclNGen_2292_ = lean_ctor_get(v___x_2288_, 3);
v_traceState_2293_ = lean_ctor_get(v___x_2288_, 4);
v_messages_2294_ = lean_ctor_get(v___x_2288_, 6);
v_infoState_2295_ = lean_ctor_get(v___x_2288_, 7);
v_snapshotTasks_2296_ = lean_ctor_get(v___x_2288_, 8);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2288_, 5);
lean_dec(v_unused_2351_);
v___x_2298_ = v___x_2288_;
v_isShared_2299_ = v_isSharedCheck_2350_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_snapshotTasks_2296_);
lean_inc(v_infoState_2295_);
lean_inc(v_messages_2294_);
lean_inc(v_traceState_2293_);
lean_inc(v_auxDeclNGen_2292_);
lean_inc(v_ngen_2291_);
lean_inc(v_nextMacroScope_2290_);
lean_inc(v_env_2289_);
lean_dec(v___x_2288_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2350_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2300_ = l_Lean_Environment_setExporting(v_env_2289_, v_isExporting_2279_);
v___x_2301_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 5, v___x_2301_);
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2303_ = v___x_2298_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_nextMacroScope_2290_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_ngen_2291_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v_auxDeclNGen_2292_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v_traceState_2293_);
lean_ctor_set(v_reuseFailAlloc_2349_, 5, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2349_, 6, v_messages_2294_);
lean_ctor_set(v_reuseFailAlloc_2349_, 7, v_infoState_2295_);
lean_ctor_set(v_reuseFailAlloc_2349_, 8, v_snapshotTasks_2296_);
v___x_2303_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v_mctx_2306_; lean_object* v_zetaDeltaFVarIds_2307_; lean_object* v_postponed_2308_; lean_object* v_diag_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2347_; 
v___x_2304_ = lean_st_ref_set(v___y_2282_, v___x_2303_);
v___x_2305_ = lean_st_ref_take(v___y_2280_);
v_mctx_2306_ = lean_ctor_get(v___x_2305_, 0);
v_zetaDeltaFVarIds_2307_ = lean_ctor_get(v___x_2305_, 2);
v_postponed_2308_ = lean_ctor_get(v___x_2305_, 3);
v_diag_2309_ = lean_ctor_get(v___x_2305_, 4);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2305_, 1);
lean_dec(v_unused_2348_);
v___x_2311_ = v___x_2305_;
v_isShared_2312_ = v_isSharedCheck_2347_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_diag_2309_);
lean_inc(v_postponed_2308_);
lean_inc(v_zetaDeltaFVarIds_2307_);
lean_inc(v_mctx_2306_);
lean_dec(v___x_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2347_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_mctx_2306_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_zetaDeltaFVarIds_2307_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_postponed_2308_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_diag_2309_);
v___x_2315_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v_r_2317_; 
v___x_2316_ = lean_st_ref_set(v___y_2280_, v___x_2315_);
v_r_2317_ = l_Lean_validateDefEqAttr(v_declName_2278_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v_r_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2334_; 
v_a_2318_ = lean_ctor_get(v_r_2317_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_r_2317_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2320_ = v_r_2317_;
v_isShared_2321_ = v_isSharedCheck_2334_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v_r_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2334_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
lean_inc(v_a_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 1);
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v___x_2324_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2282_, v_isExporting_2286_, v___x_2301_, v___y_2280_, v___x_2313_, v___x_2323_);
lean_dec_ref(v___x_2323_);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2324_, 0);
lean_dec(v_unused_2332_);
v___x_2326_ = v___x_2324_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v___x_2324_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v_a_2318_);
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2318_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2335_ = lean_ctor_get(v_r_2317_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v_r_2317_, 1);
v___x_2336_ = lean_box(0);
v___x_2337_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2282_, v_isExporting_2286_, v___x_2301_, v___y_2280_, v___x_2313_, v___x_2336_);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v___x_2337_, 0);
lean_dec(v_unused_2345_);
v___x_2339_ = v___x_2337_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v___x_2337_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 1);
lean_ctor_set(v___x_2339_, 0, v_a_2335_);
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2335_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
}
}
v___jp_2352_:
{
if (v___y_2353_ == 0)
{
goto v___jp_2287_;
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_validateDefEqAttr(v_declName_2278_, v___y_2281_, v___y_2282_);
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object* v_declName_2359_, lean_object* v_isExporting_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_isExporting_boxed_2365_; lean_object* v_res_2366_; 
v_isExporting_boxed_2365_ = lean_unbox(v_isExporting_2360_);
v_res_2366_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2359_, v_isExporting_boxed_2365_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object* v_declName_2367_, uint8_t v_isExporting_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2367_, v_isExporting_2368_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object* v_declName_2375_, lean_object* v_isExporting_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v_isExporting_boxed_2382_; lean_object* v_res_2383_; 
v_isExporting_boxed_2382_ = lean_unbox(v_isExporting_2376_);
v_res_2383_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2375_, v_isExporting_boxed_2382_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2383_;
}
}
static uint64_t _init_l_Lean_inferDefEqAttr___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2384_; uint64_t v___x_2385_; 
v___x_2384_ = 5;
v___x_2385_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* v_lhs_2386_, lean_object* v_rhs_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; uint8_t v_foApprox_2394_; uint8_t v_ctxApprox_2395_; uint8_t v_quasiPatternApprox_2396_; uint8_t v_constApprox_2397_; uint8_t v_isDefEqStuckEx_2398_; uint8_t v_unificationHints_2399_; uint8_t v_proofIrrelevance_2400_; uint8_t v_assignSyntheticOpaque_2401_; uint8_t v_offsetCnstrs_2402_; uint8_t v_etaStruct_2403_; uint8_t v_univApprox_2404_; uint8_t v_iota_2405_; uint8_t v_beta_2406_; uint8_t v_proj_2407_; uint8_t v_zeta_2408_; uint8_t v_zetaDelta_2409_; uint8_t v_zetaUnused_2410_; uint8_t v_zetaHave_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2438_; 
v___x_2393_ = l_Lean_Meta_Context_config(v___y_2388_);
v_foApprox_2394_ = lean_ctor_get_uint8(v___x_2393_, 0);
v_ctxApprox_2395_ = lean_ctor_get_uint8(v___x_2393_, 1);
v_quasiPatternApprox_2396_ = lean_ctor_get_uint8(v___x_2393_, 2);
v_constApprox_2397_ = lean_ctor_get_uint8(v___x_2393_, 3);
v_isDefEqStuckEx_2398_ = lean_ctor_get_uint8(v___x_2393_, 4);
v_unificationHints_2399_ = lean_ctor_get_uint8(v___x_2393_, 5);
v_proofIrrelevance_2400_ = lean_ctor_get_uint8(v___x_2393_, 6);
v_assignSyntheticOpaque_2401_ = lean_ctor_get_uint8(v___x_2393_, 7);
v_offsetCnstrs_2402_ = lean_ctor_get_uint8(v___x_2393_, 8);
v_etaStruct_2403_ = lean_ctor_get_uint8(v___x_2393_, 10);
v_univApprox_2404_ = lean_ctor_get_uint8(v___x_2393_, 11);
v_iota_2405_ = lean_ctor_get_uint8(v___x_2393_, 12);
v_beta_2406_ = lean_ctor_get_uint8(v___x_2393_, 13);
v_proj_2407_ = lean_ctor_get_uint8(v___x_2393_, 14);
v_zeta_2408_ = lean_ctor_get_uint8(v___x_2393_, 15);
v_zetaDelta_2409_ = lean_ctor_get_uint8(v___x_2393_, 16);
v_zetaUnused_2410_ = lean_ctor_get_uint8(v___x_2393_, 17);
v_zetaHave_2411_ = lean_ctor_get_uint8(v___x_2393_, 18);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2413_ = v___x_2393_;
v_isShared_2414_ = v_isSharedCheck_2438_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v___x_2393_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2438_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
uint8_t v_trackZetaDelta_2415_; lean_object* v_zetaDeltaSet_2416_; lean_object* v_lctx_2417_; lean_object* v_localInstances_2418_; lean_object* v_defEqCtx_x3f_2419_; lean_object* v_synthPendingDepth_2420_; lean_object* v_canUnfold_x3f_2421_; uint8_t v_univApprox_2422_; uint8_t v_inTypeClassResolution_2423_; uint8_t v_cacheInferType_2424_; uint8_t v___x_2425_; lean_object* v_config_2427_; 
v_trackZetaDelta_2415_ = lean_ctor_get_uint8(v___y_2388_, sizeof(void*)*7);
v_zetaDeltaSet_2416_ = lean_ctor_get(v___y_2388_, 1);
v_lctx_2417_ = lean_ctor_get(v___y_2388_, 2);
v_localInstances_2418_ = lean_ctor_get(v___y_2388_, 3);
v_defEqCtx_x3f_2419_ = lean_ctor_get(v___y_2388_, 4);
v_synthPendingDepth_2420_ = lean_ctor_get(v___y_2388_, 5);
v_canUnfold_x3f_2421_ = lean_ctor_get(v___y_2388_, 6);
v_univApprox_2422_ = lean_ctor_get_uint8(v___y_2388_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2423_ = lean_ctor_get_uint8(v___y_2388_, sizeof(void*)*7 + 2);
v_cacheInferType_2424_ = lean_ctor_get_uint8(v___y_2388_, sizeof(void*)*7 + 3);
v___x_2425_ = 5;
if (v_isShared_2414_ == 0)
{
v_config_2427_ = v___x_2413_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 0, v_foApprox_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 1, v_ctxApprox_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 2, v_quasiPatternApprox_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 3, v_constApprox_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 4, v_isDefEqStuckEx_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 5, v_unificationHints_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 6, v_proofIrrelevance_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 7, v_assignSyntheticOpaque_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 8, v_offsetCnstrs_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 10, v_etaStruct_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 11, v_univApprox_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 12, v_iota_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 13, v_beta_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 14, v_proj_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 15, v_zeta_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 16, v_zetaDelta_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 17, v_zetaUnused_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2437_, 18, v_zetaHave_2411_);
v_config_2427_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
uint64_t v___x_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v_key_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_ctor_set_uint8(v_config_2427_, 9, v___x_2425_);
v___x_2428_ = l_Lean_Meta_Context_configKey(v___y_2388_);
v___x_2429_ = 3ULL;
v___x_2430_ = lean_uint64_shift_right(v___x_2428_, v___x_2429_);
v___x_2431_ = lean_uint64_shift_left(v___x_2430_, v___x_2429_);
v___x_2432_ = lean_uint64_once(&l_Lean_inferDefEqAttr___lam__0___closed__0, &l_Lean_inferDefEqAttr___lam__0___closed__0_once, _init_l_Lean_inferDefEqAttr___lam__0___closed__0);
v_key_2433_ = lean_uint64_lor(v___x_2431_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2434_, 0, v_config_2427_);
lean_ctor_set_uint64(v___x_2434_, sizeof(void*)*1, v_key_2433_);
lean_inc(v_canUnfold_x3f_2421_);
lean_inc(v_synthPendingDepth_2420_);
lean_inc(v_defEqCtx_x3f_2419_);
lean_inc_ref(v_localInstances_2418_);
lean_inc_ref(v_lctx_2417_);
lean_inc(v_zetaDeltaSet_2416_);
v___x_2435_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v_zetaDeltaSet_2416_);
lean_ctor_set(v___x_2435_, 2, v_lctx_2417_);
lean_ctor_set(v___x_2435_, 3, v_localInstances_2418_);
lean_ctor_set(v___x_2435_, 4, v_defEqCtx_x3f_2419_);
lean_ctor_set(v___x_2435_, 5, v_synthPendingDepth_2420_);
lean_ctor_set(v___x_2435_, 6, v_canUnfold_x3f_2421_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7, v_trackZetaDelta_2415_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 1, v_univApprox_2422_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2423_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*7 + 3, v_cacheInferType_2424_);
v___x_2436_ = l_Lean_Meta_isExprDefEq(v_lhs_2386_, v_rhs_2387_, v___x_2435_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec_ref_known(v___x_2435_, 7);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* v_lhs_2439_, lean_object* v_rhs_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2439_, v_rhs_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__0));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__2));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* v_declName_2453_, lean_object* v___f_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___x_2470_; 
lean_inc(v_declName_2453_);
v___x_2470_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_declName_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_n(v_a_2471_, 2);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = 1;
v___x_2473_ = l_Lean_ConstantInfo_value_x3f(v_a_2471_, v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_val_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = l_Lean_ConstantInfo_type(v_a_2471_);
lean_dec(v_a_2471_);
v___x_2476_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v___x_2475_, v_val_2474_, v___y_2458_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; uint8_t v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v___x_2478_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
if (v___x_2478_ == 0)
{
lean_dec_ref(v___x_2475_);
lean_dec_ref(v___f_2454_);
lean_dec(v_declName_2453_);
goto v___jp_2467_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v___x_2475_, v___f_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___y_2486_; uint8_t v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2487_ = l_Lean_isPrivateName(v_declName_2453_);
v___x_2488_ = lean_bool_not(v___x_2487_);
lean_inc(v_declName_2453_);
v___x_2489_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2453_, v___x_2488_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2489_) == 0)
{
v___y_2486_ = v___x_2489_;
goto v___jp_2485_;
}
else
{
lean_object* v_a_2490_; uint8_t v___y_2492_; uint8_t v___x_2503_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
v___x_2503_ = l_Lean_Exception_isInterrupt(v_a_2490_);
if (v___x_2503_ == 0)
{
uint8_t v___x_2504_; 
lean_inc(v_a_2490_);
v___x_2504_ = l_Lean_Exception_isRuntime(v_a_2490_);
v___y_2492_ = v___x_2504_;
goto v___jp_2491_;
}
else
{
v___y_2492_ = v___x_2503_;
goto v___jp_2491_;
}
v___jp_2491_:
{
if (v___y_2492_ == 0)
{
uint8_t v___x_2493_; 
lean_dec_ref_known(v___x_2489_, 1);
v___x_2493_ = lean_unbox(v_a_2480_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2494_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__1, &l_Lean_inferDefEqAttr___lam__1___closed__1_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__1);
lean_inc(v_declName_2453_);
v___x_2495_ = l_Lean_MessageData_ofName(v_declName_2453_);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__3, &l_Lean_inferDefEqAttr___lam__1___closed__3_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__3);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Lean_Exception_toMessageData(v_a_2490_);
v___x_2500_ = l_Lean_indentD(v___x_2499_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v___x_2501_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v___y_2486_ = v___x_2502_;
goto v___jp_2485_;
}
else
{
lean_dec(v_a_2490_);
goto v___jp_2481_;
}
}
else
{
lean_dec(v_a_2490_);
v___y_2486_ = v___x_2489_;
goto v___jp_2485_;
}
}
}
v___jp_2481_:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_unbox(v_a_2480_);
lean_dec(v_a_2480_);
if (v___x_2482_ == 0)
{
v___y_2461_ = v___y_2455_;
v___y_2462_ = v___y_2456_;
v___y_2463_ = v___y_2457_;
v___y_2464_ = v___y_2458_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = l_Lean_defeqAttr;
lean_inc(v_declName_2453_);
v___x_2484_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2483_, v_declName_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_dec_ref_known(v___x_2484_, 1);
v___y_2461_ = v___y_2455_;
v___y_2462_ = v___y_2456_;
v___y_2463_ = v___y_2457_;
v___y_2464_ = v___y_2458_;
goto v___jp_2460_;
}
else
{
lean_dec(v_declName_2453_);
return v___x_2484_;
}
}
}
v___jp_2485_:
{
if (lean_obj_tag(v___y_2486_) == 0)
{
lean_dec_ref_known(v___y_2486_, 1);
goto v___jp_2481_;
}
else
{
lean_dec(v_a_2480_);
lean_dec(v_declName_2453_);
return v___y_2486_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_declName_2453_);
v_a_2505_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2479_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2479_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v___x_2475_);
lean_dec_ref(v___f_2454_);
lean_dec(v_declName_2453_);
v_a_2513_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2476_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2476_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_dec(v___x_2473_);
lean_dec(v_a_2471_);
lean_dec_ref(v___f_2454_);
lean_dec(v_declName_2453_);
goto v___jp_2467_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v___f_2454_);
lean_dec(v_declName_2453_);
v_a_2521_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2470_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2470_);
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
v___jp_2460_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = l_Lean_backwardDefeqAttr;
v___x_2466_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2465_, v_declName_2453_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2466_;
}
v___jp_2467_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object* v_declName_2529_, lean_object* v___f_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2529_, v___f_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object* v_declName_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___f_2544_; lean_object* v___f_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; 
v___f_2544_ = ((lean_object*)(l_Lean_inferDefEqAttr___closed__0));
v___f_2545_ = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2545_, 0, v_declName_2538_);
lean_closure_set(v___f_2545_, 1, v___f_2544_);
v___x_2546_ = 1;
v___x_2547_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___f_2545_, v___x_2546_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object* v_declName_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_inferDefEqAttr(v_declName_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_2555_, lean_object* v_attrName_2556_, lean_object* v_declName_2557_, lean_object* v_asyncPrefix_x3f_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_2556_, v_declName_2557_, v_asyncPrefix_x3f_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_attrName_2566_, lean_object* v_declName_2567_, lean_object* v_asyncPrefix_x3f_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_2565_, v_attrName_2566_, v_declName_2567_, v_asyncPrefix_x3f_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object* v_00_u03b1_2575_, lean_object* v_attrName_2576_, lean_object* v_declName_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_2576_, v_declName_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_attrName_2585_, lean_object* v_declName_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_2584_, v_attrName_2585_, v_declName_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object* v_00_u03b1_2593_, lean_object* v_constName_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2601_, lean_object* v_constName_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_2601_, v_constName_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object* v_00_u03b1_2609_, lean_object* v_ref_2610_, lean_object* v_constName_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2610_, v_constName_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2618_, lean_object* v_ref_2619_, lean_object* v_constName_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_2618_, v_ref_2619_, v_constName_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v_ref_2619_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object* v_00_u03b1_2627_, lean_object* v_ref_2628_, lean_object* v_msg_2629_, lean_object* v_declHint_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2628_, v_msg_2629_, v_declHint_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2637_, lean_object* v_ref_2638_, lean_object* v_msg_2639_, lean_object* v_declHint_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_2637_, v_ref_2638_, v_msg_2639_, v_declHint_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v_ref_2638_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(lean_object* v_msg_2647_, lean_object* v_declHint_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_2647_, v_declHint_2648_, v___y_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_2655_, lean_object* v_declHint_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(v_msg_2655_, v_declHint_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_2663_, lean_object* v_ref_2664_, lean_object* v_msg_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2664_, v_msg_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2672_, lean_object* v_ref_2673_, lean_object* v_msg_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_2672_, v_ref_2673_, v_msg_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v_ref_2673_);
return v_res_2680_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_backward_defeqAttrib_useBackward = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_backward_defeqAttrib_useBackward);
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_backwardDefeqAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_backwardDefeqAttr);
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_defeqAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_defeqAttr);
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DefEqAttrib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DefEqAttrib(builtin);
}
#ifdef __cplusplus
}
#endif
