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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1;
static lean_once_cell_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18;
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
static const lean_closure_object l_Lean_validateDefEqAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_validateDefEqAttr___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_validateDefEqAttr___closed__0 = (const lean_object*)&l_Lean_validateDefEqAttr___closed__0_value;
static const lean_ctor_object l_Lean_validateDefEqAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_validateDefEqAttr___closed__1 = (const lean_object*)&l_Lean_validateDefEqAttr___closed__1_value;
static lean_once_cell_t l_Lean_validateDefEqAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_validateDefEqAttr___closed__2;
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
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 862, .m_capacity = 862, .m_length = 861, .m_data = "Marks a theorem as a definitional equality under the permissive transparency rules that\npredated the stricter `@[defeq]` inference (i.e. an equality that holds at `.default` or\n`.all` transparency, but possibly not at `.instances` transparency as required by `dsimp`).\n\nSuch theorems are inferred automatically by `inferDefEqAttr`: any theorem that the old\n`:= rfl` inference would have accepted is tagged `@[backward_defeq]`, and additionally\ntagged `@[defeq]` when it also passes the stricter check at instance transparency.\n\n`dsimp` ignores `@[backward_defeq]` theorems by default. Setting\n`set_option backward.defeqAttrib.useBackward true` (typically scoped to a single proof\nwith `set_option ... in`) makes `dsimp` treat them like `@[defeq]` theorems, which\nprovides a local backwards-compatibility escape hatch for proofs broken by the stricter\ninference."};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(73) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(94) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
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
static const lean_string_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 774, .m_capacity = 774, .m_length = 773, .m_data = "Marks the theorem as a definitional equality that can be used by `dsimp`.\n\nThe theorem must be an equality that holds at `.implicit` transparency. A theorem\nwith a definition that is (syntactically) `:= rfl` is implicitly marked `@[defeq]`\n(and also `@[backward_defeq]`, since the latter is a superset); write `:= (rfl)`\ninstead to suppress this.\n\nThe attribute should be given before a `@[simp]` attribute to have effect.\n\nWhen using the module system, an exported theorem can only be `@[defeq]` if all\ndefinitions that need to be unfolded to prove the theorem are exported and exposed.\n\nTagging a theorem with `@[defeq]` automatically also tags it with `@[backward_defeq]`,\nmaintaining the invariant that `@[defeq]` theorems form a subset of `@[backward_defeq]`\ntheorems."};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(96) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(122) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(114) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(114) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(lean_object* v_opts_60_, lean_object* v_opt_61_){
_start:
{
lean_object* v_name_62_; lean_object* v_defValue_63_; lean_object* v_map_64_; lean_object* v___x_65_; 
v_name_62_ = lean_ctor_get(v_opt_61_, 0);
v_defValue_63_ = lean_ctor_get(v_opt_61_, 1);
v_map_64_ = lean_ctor_get(v_opts_60_, 0);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_64_, v_name_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_inc(v_defValue_63_);
return v_defValue_63_;
}
else
{
lean_object* v_val_66_; 
v_val_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v___x_65_, 1);
if (lean_obj_tag(v_val_66_) == 3)
{
lean_object* v_v_67_; 
v_v_67_ = lean_ctor_get(v_val_66_, 0);
lean_inc(v_v_67_);
lean_dec_ref_known(v_val_66_, 1);
return v_v_67_;
}
else
{
lean_dec(v_val_66_);
lean_inc(v_defValue_63_);
return v_defValue_63_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(lean_object* v_opts_68_, lean_object* v_opt_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_opts_68_, v_opt_69_);
lean_dec_ref(v_opt_69_);
lean_dec_ref(v_opts_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(lean_object* v_o_74_, lean_object* v_k_75_, uint8_t v_v_76_){
_start:
{
lean_object* v_map_77_; uint8_t v_hasTrace_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_92_; 
v_map_77_ = lean_ctor_get(v_o_74_, 0);
v_hasTrace_78_ = lean_ctor_get_uint8(v_o_74_, sizeof(void*)*1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_o_74_);
if (v_isSharedCheck_92_ == 0)
{
v___x_80_ = v_o_74_;
v_isShared_81_ = v_isSharedCheck_92_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_map_77_);
lean_dec(v_o_74_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_92_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_82_, 0, v_v_76_);
lean_inc(v_k_75_);
v___x_83_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_75_, v___x_82_, v_map_77_);
if (v_hasTrace_78_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__1));
v___x_85_ = l_Lean_Name_isPrefixOf(v___x_84_, v_k_75_);
lean_dec(v_k_75_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_87_ = v___x_80_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_83_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_85_);
return v___x_87_;
}
}
else
{
lean_object* v___x_90_; 
lean_dec(v_k_75_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_90_ = v___x_80_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_83_);
lean_ctor_set_uint8(v_reuseFailAlloc_91_, sizeof(void*)*1, v_hasTrace_78_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___boxed(lean_object* v_o_93_, lean_object* v_k_94_, lean_object* v_v_95_){
_start:
{
uint8_t v_v_boxed_96_; lean_object* v_res_97_; 
v_v_boxed_96_ = lean_unbox(v_v_95_);
v_res_97_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(v_o_93_, v_k_94_, v_v_boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(lean_object* v_opts_98_, lean_object* v_opt_99_, uint8_t v_val_100_){
_start:
{
lean_object* v_name_101_; lean_object* v___x_102_; 
v_name_101_ = lean_ctor_get(v_opt_99_, 0);
lean_inc(v_name_101_);
lean_dec_ref(v_opt_99_);
v___x_102_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(v_opts_98_, v_name_101_, v_val_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(lean_object* v_opts_103_, lean_object* v_opt_104_, lean_object* v_val_105_){
_start:
{
uint8_t v_val_boxed_106_; lean_object* v_res_107_; 
v_val_boxed_106_ = lean_unbox(v_val_105_);
v_res_107_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_opts_103_, v_opt_104_, v_val_boxed_106_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object* v_e1_113_, lean_object* v_e2_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___y_121_; lean_object* v___y_139_; lean_object* v___y_140_; lean_object* v___y_141_; lean_object* v_toCold_178_; lean_object* v_currRecDepth_179_; lean_object* v_ref_180_; uint8_t v_suppressElabErrors_181_; uint8_t v_isRecordingDeps_182_; lean_object* v_fileName_183_; lean_object* v_fileMap_184_; lean_object* v_options_185_; lean_object* v_currNamespace_186_; lean_object* v_openDecls_187_; lean_object* v_initHeartbeats_188_; lean_object* v_maxHeartbeats_189_; lean_object* v_quotContext_190_; lean_object* v_currMacroScope_191_; lean_object* v_cancelTk_x3f_192_; lean_object* v_inheritedTraceOptions_193_; uint8_t v___x_194_; lean_object* v___y_196_; uint16_t v___y_197_; lean_object* v_fileName_198_; lean_object* v_fileMap_199_; lean_object* v_currNamespace_200_; lean_object* v_openDecls_201_; lean_object* v_initHeartbeats_202_; lean_object* v_maxHeartbeats_203_; lean_object* v_quotContext_204_; lean_object* v_currMacroScope_205_; lean_object* v_cancelTk_x3f_206_; lean_object* v_inheritedTraceOptions_207_; lean_object* v_currRecDepth_208_; lean_object* v_ref_209_; uint8_t v_suppressElabErrors_210_; uint8_t v_isRecordingDeps_211_; lean_object* v___y_212_; lean_object* v___y_236_; uint8_t v___y_237_; uint16_t v___y_238_; lean_object* v___y_261_; 
v_toCold_178_ = lean_ctor_get(v_a_117_, 0);
v_currRecDepth_179_ = lean_ctor_get(v_a_117_, 1);
v_ref_180_ = lean_ctor_get(v_a_117_, 2);
v_suppressElabErrors_181_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*3 + 2);
v_isRecordingDeps_182_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*3 + 3);
v_fileName_183_ = lean_ctor_get(v_toCold_178_, 0);
v_fileMap_184_ = lean_ctor_get(v_toCold_178_, 1);
v_options_185_ = lean_ctor_get(v_toCold_178_, 2);
v_currNamespace_186_ = lean_ctor_get(v_toCold_178_, 4);
v_openDecls_187_ = lean_ctor_get(v_toCold_178_, 5);
v_initHeartbeats_188_ = lean_ctor_get(v_toCold_178_, 6);
v_maxHeartbeats_189_ = lean_ctor_get(v_toCold_178_, 7);
v_quotContext_190_ = lean_ctor_get(v_toCold_178_, 8);
v_currMacroScope_191_ = lean_ctor_get(v_toCold_178_, 9);
v_cancelTk_x3f_192_ = lean_ctor_get(v_toCold_178_, 10);
v_inheritedTraceOptions_193_ = lean_ctor_get(v_toCold_178_, 11);
v___x_194_ = 1;
if (v_isRecordingDeps_182_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_185_);
v___x_273_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_185_, v___x_272_, v_isRecordingDeps_182_);
v___y_261_ = v___x_273_;
goto v___jp_260_;
}
else
{
lean_object* v___x_274_; 
lean_inc_ref(v_options_185_);
v___x_274_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_185_);
v___y_261_ = v___x_274_;
goto v___jp_260_;
}
v___jp_120_:
{
if (lean_obj_tag(v___y_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___y_121_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___y_121_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___y_121_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___y_121_);
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
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___y_121_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___y_121_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___y_121_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___y_121_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
v___jp_138_:
{
if (lean_obj_tag(v___y_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_169_; 
v_a_142_ = lean_ctor_get(v___y_141_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___y_141_);
if (v_isSharedCheck_169_ == 0)
{
v___x_144_ = v___y_141_;
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___y_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
uint8_t v___x_146_; 
v___x_146_ = lean_unbox(v_a_142_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint8_t v_transparency_148_; uint8_t v___x_149_; uint8_t v___x_150_; 
lean_del_object(v___x_144_);
lean_dec(v_a_142_);
v___x_147_ = l_Lean_Meta_Context_config(v_a_115_);
v_transparency_148_ = lean_ctor_get_uint8(v___x_147_, 9);
lean_dec_ref(v___x_147_);
v___x_149_ = 0;
v___x_150_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v_keyedConfig_151_; uint8_t v_trackZetaDelta_152_; lean_object* v_zetaDeltaSet_153_; lean_object* v_lctx_154_; lean_object* v_localInstances_155_; lean_object* v_defEqCtx_x3f_156_; lean_object* v_synthPendingDepth_157_; lean_object* v_customCanUnfoldPredicate_x3f_158_; uint8_t v_univApprox_159_; uint8_t v_inTypeClassResolution_160_; uint8_t v_cacheInferType_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_keyedConfig_151_ = lean_ctor_get(v_a_115_, 0);
v_trackZetaDelta_152_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7);
v_zetaDeltaSet_153_ = lean_ctor_get(v_a_115_, 1);
v_lctx_154_ = lean_ctor_get(v_a_115_, 2);
v_localInstances_155_ = lean_ctor_get(v_a_115_, 3);
v_defEqCtx_x3f_156_ = lean_ctor_get(v_a_115_, 4);
v_synthPendingDepth_157_ = lean_ctor_get(v_a_115_, 5);
v_customCanUnfoldPredicate_x3f_158_ = lean_ctor_get(v_a_115_, 6);
v_univApprox_159_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_160_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 2);
v_cacheInferType_161_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_151_);
v___x_162_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_149_, v_keyedConfig_151_);
lean_inc(v_customCanUnfoldPredicate_x3f_158_);
lean_inc(v_synthPendingDepth_157_);
lean_inc(v_defEqCtx_x3f_156_);
lean_inc_ref(v_localInstances_155_);
lean_inc_ref(v_lctx_154_);
lean_inc(v_zetaDeltaSet_153_);
v___x_163_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_zetaDeltaSet_153_);
lean_ctor_set(v___x_163_, 2, v_lctx_154_);
lean_ctor_set(v___x_163_, 3, v_localInstances_155_);
lean_ctor_set(v___x_163_, 4, v_defEqCtx_x3f_156_);
lean_ctor_set(v___x_163_, 5, v_synthPendingDepth_157_);
lean_ctor_set(v___x_163_, 6, v_customCanUnfoldPredicate_x3f_158_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7, v_trackZetaDelta_152_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 1, v_univApprox_159_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 2, v_inTypeClassResolution_160_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*7 + 3, v_cacheInferType_161_);
v___x_164_ = l_Lean_Meta_isExprDefEq(v_e1_113_, v_e2_114_, v___x_163_, v_a_116_, v___y_139_, v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec_ref_known(v___x_163_, 7);
v___y_121_ = v___x_164_;
goto v___jp_120_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_isExprDefEq(v_e1_113_, v_e2_114_, v_a_115_, v_a_116_, v___y_139_, v___y_140_);
lean_dec_ref(v___y_139_);
v___y_121_ = v___x_165_;
goto v___jp_120_;
}
}
else
{
lean_object* v___x_167_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_e2_114_);
lean_dec_ref(v_e1_113_);
if (v_isShared_145_ == 0)
{
v___x_167_ = v___x_144_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_142_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec_ref(v___y_139_);
lean_dec_ref(v_e2_114_);
lean_dec_ref(v_e1_113_);
v_a_170_ = lean_ctor_get(v___y_141_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___y_141_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___y_141_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___y_141_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
v___jp_195_:
{
lean_object* v___x_213_; uint8_t v_transparency_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_213_ = l_Lean_Meta_Context_config(v_a_115_);
v_transparency_214_ = lean_ctor_get_uint8(v___x_213_, 9);
lean_dec_ref(v___x_213_);
v___x_215_ = l_Lean_maxRecDepth;
v___x_216_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v___y_196_, v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_217_, 0, v_fileName_198_);
lean_ctor_set(v___x_217_, 1, v_fileMap_199_);
lean_ctor_set(v___x_217_, 2, v___y_196_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
lean_ctor_set(v___x_217_, 4, v_currNamespace_200_);
lean_ctor_set(v___x_217_, 5, v_openDecls_201_);
lean_ctor_set(v___x_217_, 6, v_initHeartbeats_202_);
lean_ctor_set(v___x_217_, 7, v_maxHeartbeats_203_);
lean_ctor_set(v___x_217_, 8, v_quotContext_204_);
lean_ctor_set(v___x_217_, 9, v_currMacroScope_205_);
lean_ctor_set(v___x_217_, 10, v_cancelTk_x3f_206_);
lean_ctor_set(v___x_217_, 11, v_inheritedTraceOptions_207_);
lean_inc(v_ref_209_);
lean_inc(v_currRecDepth_208_);
v___x_218_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_currRecDepth_208_);
lean_ctor_set(v___x_218_, 2, v_ref_209_);
lean_ctor_set_uint16(v___x_218_, sizeof(void*)*3, v___y_197_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*3 + 2, v_suppressElabErrors_210_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*3 + 3, v_isRecordingDeps_211_);
v___x_219_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_214_, v___x_194_);
if (v___x_219_ == 0)
{
lean_object* v_keyedConfig_220_; uint8_t v_trackZetaDelta_221_; lean_object* v_zetaDeltaSet_222_; lean_object* v_lctx_223_; lean_object* v_localInstances_224_; lean_object* v_defEqCtx_x3f_225_; lean_object* v_synthPendingDepth_226_; lean_object* v_customCanUnfoldPredicate_x3f_227_; uint8_t v_univApprox_228_; uint8_t v_inTypeClassResolution_229_; uint8_t v_cacheInferType_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_keyedConfig_220_ = lean_ctor_get(v_a_115_, 0);
v_trackZetaDelta_221_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7);
v_zetaDeltaSet_222_ = lean_ctor_get(v_a_115_, 1);
v_lctx_223_ = lean_ctor_get(v_a_115_, 2);
v_localInstances_224_ = lean_ctor_get(v_a_115_, 3);
v_defEqCtx_x3f_225_ = lean_ctor_get(v_a_115_, 4);
v_synthPendingDepth_226_ = lean_ctor_get(v_a_115_, 5);
v_customCanUnfoldPredicate_x3f_227_ = lean_ctor_get(v_a_115_, 6);
v_univApprox_228_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_229_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 2);
v_cacheInferType_230_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_220_);
v___x_231_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_194_, v_keyedConfig_220_);
lean_inc(v_customCanUnfoldPredicate_x3f_227_);
lean_inc(v_synthPendingDepth_226_);
lean_inc(v_defEqCtx_x3f_225_);
lean_inc_ref(v_localInstances_224_);
lean_inc_ref(v_lctx_223_);
lean_inc(v_zetaDeltaSet_222_);
v___x_232_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_zetaDeltaSet_222_);
lean_ctor_set(v___x_232_, 2, v_lctx_223_);
lean_ctor_set(v___x_232_, 3, v_localInstances_224_);
lean_ctor_set(v___x_232_, 4, v_defEqCtx_x3f_225_);
lean_ctor_set(v___x_232_, 5, v_synthPendingDepth_226_);
lean_ctor_set(v___x_232_, 6, v_customCanUnfoldPredicate_x3f_227_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*7, v_trackZetaDelta_221_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*7 + 1, v_univApprox_228_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*7 + 2, v_inTypeClassResolution_229_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*7 + 3, v_cacheInferType_230_);
lean_inc_ref(v_e2_114_);
lean_inc_ref(v_e1_113_);
v___x_233_ = l_Lean_Meta_isExprDefEq(v_e1_113_, v_e2_114_, v___x_232_, v_a_116_, v___x_218_, v___y_212_);
lean_dec_ref_known(v___x_232_, 7);
v___y_139_ = v___x_218_;
v___y_140_ = v___y_212_;
v___y_141_ = v___x_233_;
goto v___jp_138_;
}
else
{
lean_object* v___x_234_; 
lean_inc_ref(v_e2_114_);
lean_inc_ref(v_e1_113_);
v___x_234_ = l_Lean_Meta_isExprDefEq(v_e1_113_, v_e2_114_, v_a_115_, v_a_116_, v___x_218_, v___y_212_);
v___y_139_ = v___x_218_;
v___y_140_ = v___y_212_;
v___y_141_ = v___x_234_;
goto v___jp_138_;
}
}
v___jp_235_:
{
lean_object* v___x_239_; lean_object* v_env_240_; lean_object* v_nextMacroScope_241_; lean_object* v_ngen_242_; lean_object* v_auxDeclNGen_243_; lean_object* v_traceState_244_; lean_object* v_recordedDeps_245_; lean_object* v_messages_246_; lean_object* v_infoState_247_; lean_object* v_snapshotTasks_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_258_; 
v___x_239_ = lean_st_ref_take(v_a_118_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
v_nextMacroScope_241_ = lean_ctor_get(v___x_239_, 1);
v_ngen_242_ = lean_ctor_get(v___x_239_, 2);
v_auxDeclNGen_243_ = lean_ctor_get(v___x_239_, 3);
v_traceState_244_ = lean_ctor_get(v___x_239_, 4);
v_recordedDeps_245_ = lean_ctor_get(v___x_239_, 6);
v_messages_246_ = lean_ctor_get(v___x_239_, 7);
v_infoState_247_ = lean_ctor_get(v___x_239_, 8);
v_snapshotTasks_248_ = lean_ctor_get(v___x_239_, 9);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_239_, 5);
lean_dec(v_unused_259_);
v___x_250_ = v___x_239_;
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snapshotTasks_248_);
lean_inc(v_infoState_247_);
lean_inc(v_messages_246_);
lean_inc(v_recordedDeps_245_);
lean_inc(v_traceState_244_);
lean_inc(v_auxDeclNGen_243_);
lean_inc(v_ngen_242_);
lean_inc(v_nextMacroScope_241_);
lean_inc(v_env_240_);
lean_dec(v___x_239_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_252_ = l_Lean_Kernel_enableDiag(v_env_240_, v___y_237_);
v___x_253_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 5, v___x_253_);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_241_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_242_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_traceState_244_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_recordedDeps_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v_messages_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_infoState_247_);
lean_ctor_set(v_reuseFailAlloc_257_, 9, v_snapshotTasks_248_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_st_ref_put(v_a_118_, v___x_255_);
lean_inc_ref(v_inheritedTraceOptions_193_);
lean_inc(v_cancelTk_x3f_192_);
lean_inc(v_currMacroScope_191_);
lean_inc(v_quotContext_190_);
lean_inc(v_maxHeartbeats_189_);
lean_inc(v_initHeartbeats_188_);
lean_inc(v_openDecls_187_);
lean_inc(v_currNamespace_186_);
lean_inc_ref(v_fileMap_184_);
lean_inc_ref(v_fileName_183_);
v___y_196_ = v___y_236_;
v___y_197_ = v___y_238_;
v_fileName_198_ = v_fileName_183_;
v_fileMap_199_ = v_fileMap_184_;
v_currNamespace_200_ = v_currNamespace_186_;
v_openDecls_201_ = v_openDecls_187_;
v_initHeartbeats_202_ = v_initHeartbeats_188_;
v_maxHeartbeats_203_ = v_maxHeartbeats_189_;
v_quotContext_204_ = v_quotContext_190_;
v_currMacroScope_205_ = v_currMacroScope_191_;
v_cancelTk_x3f_206_ = v_cancelTk_x3f_192_;
v_inheritedTraceOptions_207_ = v_inheritedTraceOptions_193_;
v_currRecDepth_208_ = v_currRecDepth_179_;
v_ref_209_ = v_ref_180_;
v_suppressElabErrors_210_ = v_suppressElabErrors_181_;
v_isRecordingDeps_211_ = v_isRecordingDeps_182_;
v___y_212_ = v_a_118_;
goto v___jp_195_;
}
}
}
v___jp_260_:
{
uint16_t v___x_262_; lean_object* v___x_263_; lean_object* v_env_264_; uint8_t v___x_265_; uint16_t v___x_266_; uint16_t v___x_267_; uint16_t v___x_268_; uint8_t v___x_269_; 
v___x_262_ = l_Lean_OptionFlags_ofOptions(v___y_261_);
v___x_263_ = lean_st_ref_get(v_a_118_);
v_env_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc_ref(v_env_264_);
lean_dec(v___x_263_);
v___x_265_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_264_);
lean_dec_ref(v_env_264_);
v___x_266_ = 512;
v___x_267_ = lean_uint16_land(v___x_262_, v___x_266_);
v___x_268_ = 0;
v___x_269_ = lean_uint16_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
if (v___x_265_ == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 1;
v___y_236_ = v___y_261_;
v___y_237_ = v___x_270_;
v___y_238_ = v___x_262_;
goto v___jp_235_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_193_);
lean_inc(v_cancelTk_x3f_192_);
lean_inc(v_currMacroScope_191_);
lean_inc(v_quotContext_190_);
lean_inc(v_maxHeartbeats_189_);
lean_inc(v_initHeartbeats_188_);
lean_inc(v_openDecls_187_);
lean_inc(v_currNamespace_186_);
lean_inc_ref(v_fileMap_184_);
lean_inc_ref(v_fileName_183_);
v___y_196_ = v___y_261_;
v___y_197_ = v___x_262_;
v_fileName_198_ = v_fileName_183_;
v_fileMap_199_ = v_fileMap_184_;
v_currNamespace_200_ = v_currNamespace_186_;
v_openDecls_201_ = v_openDecls_187_;
v_initHeartbeats_202_ = v_initHeartbeats_188_;
v_maxHeartbeats_203_ = v_maxHeartbeats_189_;
v_quotContext_204_ = v_quotContext_190_;
v_currMacroScope_205_ = v_currMacroScope_191_;
v_cancelTk_x3f_206_ = v_cancelTk_x3f_192_;
v_inheritedTraceOptions_207_ = v_inheritedTraceOptions_193_;
v_currRecDepth_208_ = v_currRecDepth_179_;
v_ref_209_ = v_ref_180_;
v_suppressElabErrors_210_ = v_suppressElabErrors_181_;
v_isRecordingDeps_211_ = v_isRecordingDeps_182_;
v___y_212_ = v_a_118_;
goto v___jp_195_;
}
}
else
{
if (v___x_265_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_193_);
lean_inc(v_cancelTk_x3f_192_);
lean_inc(v_currMacroScope_191_);
lean_inc(v_quotContext_190_);
lean_inc(v_maxHeartbeats_189_);
lean_inc(v_initHeartbeats_188_);
lean_inc(v_openDecls_187_);
lean_inc(v_currNamespace_186_);
lean_inc_ref(v_fileMap_184_);
lean_inc_ref(v_fileName_183_);
v___y_196_ = v___y_261_;
v___y_197_ = v___x_262_;
v_fileName_198_ = v_fileName_183_;
v_fileMap_199_ = v_fileMap_184_;
v_currNamespace_200_ = v_currNamespace_186_;
v_openDecls_201_ = v_openDecls_187_;
v_initHeartbeats_202_ = v_initHeartbeats_188_;
v_maxHeartbeats_203_ = v_maxHeartbeats_189_;
v_quotContext_204_ = v_quotContext_190_;
v_currMacroScope_205_ = v_currMacroScope_191_;
v_cancelTk_x3f_206_ = v_cancelTk_x3f_192_;
v_inheritedTraceOptions_207_ = v_inheritedTraceOptions_193_;
v_currRecDepth_208_ = v_currRecDepth_179_;
v_ref_209_ = v_ref_180_;
v_suppressElabErrors_210_ = v_suppressElabErrors_181_;
v_isRecordingDeps_211_ = v_isRecordingDeps_182_;
v___y_212_ = v_a_118_;
goto v___jp_195_;
}
else
{
uint8_t v___x_271_; 
v___x_271_ = 0;
v___y_236_ = v___y_261_;
v___y_237_ = v___x_271_;
v___y_238_ = v___x_262_;
goto v___jp_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(lean_object* v_e1_275_, lean_object* v_e2_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_e1_275_, v_e2_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(lean_object* v_k_283_, lean_object* v_b_284_, lean_object* v_c_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
v___x_291_ = lean_apply_7(v_k_283_, v_b_284_, v_c_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, lean_box(0));
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(lean_object* v_k_292_, lean_object* v_b_293_, lean_object* v_c_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_292_, v_b_293_, v_c_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(lean_object* v_type_301_, lean_object* v_k_302_, uint8_t v_cleanupAnnotations_303_, uint8_t v_whnfType_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___f_310_; lean_object* v___x_311_; 
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_310_, 0, v_k_302_);
v___x_311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_301_, v___f_310_, v_cleanupAnnotations_303_, v_whnfType_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_311_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_311_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(lean_object* v_type_328_, lean_object* v_k_329_, lean_object* v_cleanupAnnotations_330_, lean_object* v_whnfType_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_337_; uint8_t v_whnfType_boxed_338_; lean_object* v_res_339_; 
v_cleanupAnnotations_boxed_337_ = lean_unbox(v_cleanupAnnotations_330_);
v_whnfType_boxed_338_ = lean_unbox(v_whnfType_331_);
v_res_339_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_328_, v_k_329_, v_cleanupAnnotations_boxed_337_, v_whnfType_boxed_338_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_object* v_00_u03b1_340_, lean_object* v_type_341_, lean_object* v_k_342_, uint8_t v_cleanupAnnotations_343_, uint8_t v_whnfType_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_341_, v_k_342_, v_cleanupAnnotations_343_, v_whnfType_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(lean_object* v_00_u03b1_351_, lean_object* v_type_352_, lean_object* v_k_353_, lean_object* v_cleanupAnnotations_354_, lean_object* v_whnfType_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_361_; uint8_t v_whnfType_boxed_362_; lean_object* v_res_363_; 
v_cleanupAnnotations_boxed_361_ = lean_unbox(v_cleanupAnnotations_354_);
v_whnfType_boxed_362_ = lean_unbox(v_whnfType_355_);
v_res_363_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(v_00_u03b1_351_, v_type_352_, v_k_353_, v_cleanupAnnotations_boxed_361_, v_whnfType_boxed_362_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; lean_object* v_toCold_373_; lean_object* v_mctx_374_; lean_object* v_lctx_375_; lean_object* v_options_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_370_ = lean_st_ref_get(v___y_368_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = lean_st_ref_get(v___y_366_);
v_toCold_373_ = lean_ctor_get(v___y_367_, 0);
v_mctx_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_mctx_374_);
lean_dec(v___x_372_);
v_lctx_375_ = lean_ctor_get(v___y_365_, 2);
v_options_376_ = lean_ctor_get(v_toCold_373_, 2);
lean_inc_ref(v_options_376_);
lean_inc_ref(v_lctx_375_);
v___x_377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_377_, 0, v_env_371_);
lean_ctor_set(v___x_377_, 1, v_mctx_374_);
lean_ctor_set(v___x_377_, 2, v_lctx_375_);
lean_ctor_set(v___x_377_, 3, v_options_376_);
v___x_378_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_msgData_364_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_ref_393_ = lean_ctor_get(v___y_390_, 2);
v___x_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_ref_393_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_393_);
lean_ctor_set(v___x_399_, 1, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(lean_object* v_k_417_, lean_object* v_x_418_, lean_object* v_type_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_425_ = lean_whnf(v_type_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_428_ = lean_unsigned_to_nat(3u);
v___x_429_ = l_Lean_Expr_isAppOfArity(v_a_426_, v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v_k_417_);
v___x_430_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3);
v___x_431_ = lean_unsigned_to_nat(30u);
v___x_432_ = l_Lean_inlineExpr(v_a_426_, v___x_431_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_430_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_433_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = l_Lean_Expr_appFn_x21(v_a_426_);
v___x_436_ = l_Lean_Expr_appArg_x21(v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = l_Lean_Expr_appArg_x21(v_a_426_);
lean_dec(v_a_426_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_438_ = lean_apply_7(v_k_417_, v___x_436_, v___x_437_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
return v___x_438_;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_k_417_);
v_a_439_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_425_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_425_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(lean_object* v_k_447_, lean_object* v_x_448_, lean_object* v_type_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(v_k_447_, v_x_448_, v_type_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v_x_448_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(lean_object* v_type_456_, lean_object* v_k_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___y_464_; lean_object* v___x_481_; uint8_t v_transparency_482_; lean_object* v___f_483_; uint8_t v___x_484_; uint8_t v___x_485_; uint8_t v___x_486_; 
v___x_481_ = l_Lean_Meta_Context_config(v_a_458_);
v_transparency_482_ = lean_ctor_get_uint8(v___x_481_, 9);
lean_dec_ref(v___x_481_);
v___f_483_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_483_, 0, v_k_457_);
v___x_484_ = 0;
v___x_485_ = 0;
v___x_486_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_482_, v___x_484_);
if (v___x_486_ == 0)
{
lean_object* v_keyedConfig_487_; uint8_t v_trackZetaDelta_488_; lean_object* v_zetaDeltaSet_489_; lean_object* v_lctx_490_; lean_object* v_localInstances_491_; lean_object* v_defEqCtx_x3f_492_; lean_object* v_synthPendingDepth_493_; lean_object* v_customCanUnfoldPredicate_x3f_494_; uint8_t v_univApprox_495_; uint8_t v_inTypeClassResolution_496_; uint8_t v_cacheInferType_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_keyedConfig_487_ = lean_ctor_get(v_a_458_, 0);
v_trackZetaDelta_488_ = lean_ctor_get_uint8(v_a_458_, sizeof(void*)*7);
v_zetaDeltaSet_489_ = lean_ctor_get(v_a_458_, 1);
v_lctx_490_ = lean_ctor_get(v_a_458_, 2);
v_localInstances_491_ = lean_ctor_get(v_a_458_, 3);
v_defEqCtx_x3f_492_ = lean_ctor_get(v_a_458_, 4);
v_synthPendingDepth_493_ = lean_ctor_get(v_a_458_, 5);
v_customCanUnfoldPredicate_x3f_494_ = lean_ctor_get(v_a_458_, 6);
v_univApprox_495_ = lean_ctor_get_uint8(v_a_458_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_496_ = lean_ctor_get_uint8(v_a_458_, sizeof(void*)*7 + 2);
v_cacheInferType_497_ = lean_ctor_get_uint8(v_a_458_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_487_);
v___x_498_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_484_, v_keyedConfig_487_);
lean_inc(v_customCanUnfoldPredicate_x3f_494_);
lean_inc(v_synthPendingDepth_493_);
lean_inc(v_defEqCtx_x3f_492_);
lean_inc_ref(v_localInstances_491_);
lean_inc_ref(v_lctx_490_);
lean_inc(v_zetaDeltaSet_489_);
v___x_499_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_zetaDeltaSet_489_);
lean_ctor_set(v___x_499_, 2, v_lctx_490_);
lean_ctor_set(v___x_499_, 3, v_localInstances_491_);
lean_ctor_set(v___x_499_, 4, v_defEqCtx_x3f_492_);
lean_ctor_set(v___x_499_, 5, v_synthPendingDepth_493_);
lean_ctor_set(v___x_499_, 6, v_customCanUnfoldPredicate_x3f_494_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*7, v_trackZetaDelta_488_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*7 + 1, v_univApprox_495_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*7 + 2, v_inTypeClassResolution_496_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*7 + 3, v_cacheInferType_497_);
v___x_500_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_456_, v___f_483_, v___x_485_, v___x_485_, v___x_499_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref_known(v___x_499_, 7);
v___y_464_ = v___x_500_;
goto v___jp_463_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_456_, v___f_483_, v___x_485_, v___x_485_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
v___y_464_ = v___x_501_;
goto v___jp_463_;
}
v___jp_463_:
{
if (lean_obj_tag(v___y_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___y_464_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___y_464_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___y_464_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___y_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___y_464_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_464_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___y_464_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___y_464_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(lean_object* v_type_502_, lean_object* v_k_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_502_, v_k_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_object* v_00_u03b1_510_, lean_object* v_type_511_, lean_object* v_k_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_511_, v_k_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(lean_object* v_00_u03b1_519_, lean_object* v_type_520_, lean_object* v_k_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(v_00_u03b1_519_, v_type_520_, v_k_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_object* v_00_u03b1_528_, lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(lean_object* v_00_u03b1_536_, lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(v_00_u03b1_536_, v_msg_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(lean_object* v___y_544_, uint8_t v_isExporting_545_, lean_object* v___x_546_, lean_object* v___y_547_, lean_object* v___x_548_, lean_object* v_a_x3f_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_traceState_556_; lean_object* v_recordedDeps_557_; lean_object* v_messages_558_; lean_object* v_infoState_559_; lean_object* v_snapshotTasks_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_585_; 
v___x_551_ = lean_st_ref_take(v___y_544_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_551_, 1);
v_ngen_554_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_551_, 3);
v_traceState_556_ = lean_ctor_get(v___x_551_, 4);
v_recordedDeps_557_ = lean_ctor_get(v___x_551_, 6);
v_messages_558_ = lean_ctor_get(v___x_551_, 7);
v_infoState_559_ = lean_ctor_get(v___x_551_, 8);
v_snapshotTasks_560_ = lean_ctor_get(v___x_551_, 9);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v___x_551_, 5);
lean_dec(v_unused_586_);
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_585_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snapshotTasks_560_);
lean_inc(v_infoState_559_);
lean_inc(v_messages_558_);
lean_inc(v_recordedDeps_557_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_585_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Environment_setExporting(v_env_552_, v_isExporting_545_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 5, v___x_546_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_traceState_556_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_584_, 6, v_recordedDeps_557_);
lean_ctor_set(v_reuseFailAlloc_584_, 7, v_messages_558_);
lean_ctor_set(v_reuseFailAlloc_584_, 8, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_584_, 9, v_snapshotTasks_560_);
v___x_566_ = v_reuseFailAlloc_584_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_mctx_569_; lean_object* v_zetaDeltaFVarIds_570_; lean_object* v_postponed_571_; lean_object* v_diag_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_582_; 
v___x_567_ = lean_st_ref_put(v___y_544_, v___x_566_);
v___x_568_ = lean_st_ref_take(v___y_547_);
v_mctx_569_ = lean_ctor_get(v___x_568_, 0);
v_zetaDeltaFVarIds_570_ = lean_ctor_get(v___x_568_, 2);
v_postponed_571_ = lean_ctor_get(v___x_568_, 3);
v_diag_572_ = lean_ctor_get(v___x_568_, 4);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_568_, 1);
lean_dec(v_unused_583_);
v___x_574_ = v___x_568_;
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_diag_572_);
lean_inc(v_postponed_571_);
lean_inc(v_zetaDeltaFVarIds_570_);
lean_inc(v_mctx_569_);
lean_dec(v___x_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_582_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___x_548_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_mctx_569_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_zetaDeltaFVarIds_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_postponed_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_diag_572_);
v___x_578_ = v_reuseFailAlloc_581_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_st_ref_put(v___y_547_, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_576_);
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___y_587_, lean_object* v_isExporting_588_, lean_object* v___x_589_, lean_object* v___y_590_, lean_object* v___x_591_, lean_object* v_a_x3f_592_, lean_object* v___y_593_){
_start:
{
uint8_t v_isExporting_boxed_594_; lean_object* v_res_595_; 
v_isExporting_boxed_594_ = lean_unbox(v_isExporting_588_);
v_res_595_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_587_, v_isExporting_boxed_594_, v___x_589_, v___y_590_, v___x_591_, v_a_x3f_592_);
lean_dec(v_a_x3f_592_);
lean_dec(v___y_590_);
lean_dec(v___y_587_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_597_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
lean_ctor_set(v___x_597_, 3, v___x_596_);
lean_ctor_set(v___x_597_, 4, v___x_596_);
lean_ctor_set(v___x_597_, 5, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object* v_x_598_, uint8_t v_isExporting_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v___x_607_; uint8_t v_isModule_608_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v___x_607_ = l_Lean_Environment_header(v_env_606_);
v_isModule_608_ = lean_ctor_get_uint8(v___x_607_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_607_);
if (v_isModule_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_env_606_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_609_ = lean_apply_5(v_x_598_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
return v___x_609_;
}
else
{
uint8_t v_isExporting_610_; 
v_isExporting_610_ = lean_ctor_get_uint8(v_env_606_, sizeof(void*)*8);
lean_dec_ref(v_env_606_);
if (v_isExporting_599_ == 0)
{
if (v_isExporting_610_ == 0)
{
lean_object* v___x_677_; 
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_677_ = lean_apply_5(v_x_598_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
return v___x_677_;
}
else
{
goto v___jp_611_;
}
}
else
{
if (v_isExporting_610_ == 0)
{
goto v___jp_611_;
}
else
{
lean_object* v___x_678_; 
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_678_ = lean_apply_5(v_x_598_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
return v___x_678_;
}
}
v___jp_611_:
{
lean_object* v___x_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_traceState_617_; lean_object* v_recordedDeps_618_; lean_object* v_messages_619_; lean_object* v_infoState_620_; lean_object* v_snapshotTasks_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_675_; 
v___x_612_ = lean_st_ref_take(v___y_603_);
v_env_613_ = lean_ctor_get(v___x_612_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_612_, 1);
v_ngen_615_ = lean_ctor_get(v___x_612_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_612_, 3);
v_traceState_617_ = lean_ctor_get(v___x_612_, 4);
v_recordedDeps_618_ = lean_ctor_get(v___x_612_, 6);
v_messages_619_ = lean_ctor_get(v___x_612_, 7);
v_infoState_620_ = lean_ctor_get(v___x_612_, 8);
v_snapshotTasks_621_ = lean_ctor_get(v___x_612_, 9);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_612_, 5);
lean_dec(v_unused_676_);
v___x_623_ = v___x_612_;
v_isShared_624_ = v_isSharedCheck_675_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snapshotTasks_621_);
lean_inc(v_infoState_620_);
lean_inc(v_messages_619_);
lean_inc(v_recordedDeps_618_);
lean_inc(v_traceState_617_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_675_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = l_Lean_Environment_setExporting(v_env_613_, v_isExporting_599_);
v___x_626_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 5, v___x_626_);
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_traceState_617_);
lean_ctor_set(v_reuseFailAlloc_674_, 5, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_674_, 6, v_recordedDeps_618_);
lean_ctor_set(v_reuseFailAlloc_674_, 7, v_messages_619_);
lean_ctor_set(v_reuseFailAlloc_674_, 8, v_infoState_620_);
lean_ctor_set(v_reuseFailAlloc_674_, 9, v_snapshotTasks_621_);
v___x_628_ = v_reuseFailAlloc_674_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_mctx_631_; lean_object* v_zetaDeltaFVarIds_632_; lean_object* v_postponed_633_; lean_object* v_diag_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_672_; 
v___x_629_ = lean_st_ref_put(v___y_603_, v___x_628_);
v___x_630_ = lean_st_ref_take(v___y_601_);
v_mctx_631_ = lean_ctor_get(v___x_630_, 0);
v_zetaDeltaFVarIds_632_ = lean_ctor_get(v___x_630_, 2);
v_postponed_633_ = lean_ctor_get(v___x_630_, 3);
v_diag_634_ = lean_ctor_get(v___x_630_, 4);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_630_, 1);
lean_dec(v_unused_673_);
v___x_636_ = v___x_630_;
v_isShared_637_ = v_isSharedCheck_672_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_diag_634_);
lean_inc(v_postponed_633_);
lean_inc(v_zetaDeltaFVarIds_632_);
lean_inc(v_mctx_631_);
lean_dec(v___x_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_672_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_mctx_631_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_zetaDeltaFVarIds_632_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_postponed_633_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_diag_634_);
v___x_640_ = v_reuseFailAlloc_671_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v_r_642_; 
v___x_641_ = lean_st_ref_put(v___y_601_, v___x_640_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v_r_642_ = lean_apply_5(v_x_598_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
if (lean_obj_tag(v_r_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_659_; 
v_a_643_ = lean_ctor_get(v_r_642_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_r_642_);
if (v_isSharedCheck_659_ == 0)
{
v___x_645_ = v_r_642_;
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v_r_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
lean_inc(v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 1);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_658_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v___x_649_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_603_, v_isExporting_610_, v___x_626_, v___y_601_, v___x_638_, v___x_648_);
lean_dec_ref(v___x_648_);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_657_);
v___x_651_ = v___x_649_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_dec(v___x_649_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_a_643_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_643_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_660_ = lean_ctor_get(v_r_642_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v_r_642_, 1);
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_603_, v_isExporting_610_, v___x_626_, v___y_601_, v___x_638_, v___x_661_);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_662_, 0);
lean_dec(v_unused_670_);
v___x_664_ = v___x_662_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_662_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 1);
lean_ctor_set(v___x_664_, 0, v_a_660_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_660_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_679_, lean_object* v_isExporting_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v_isExporting_boxed_686_; lean_object* v_res_687_; 
v_isExporting_boxed_686_ = lean_unbox(v_isExporting_680_);
v_res_687_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_679_, v_isExporting_boxed_686_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object* v_x_688_, uint8_t v_when_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
if (v_when_689_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
v___x_695_ = lean_apply_5(v_x_688_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
return v___x_695_;
}
else
{
uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_696_ = 0;
v___x_697_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_688_, v___x_696_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object* v_x_698_, lean_object* v_when_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_when_boxed_705_; lean_object* v_res_706_; 
v_when_boxed_705_ = lean_unbox(v_when_699_);
v_res_706_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_698_, v_when_boxed_705_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_706_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__0));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__2));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__4));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__5, &l_Lean_validateDefEqAttr___lam__0___closed__5_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__5);
v___x_717_ = l_Lean_MessageData_note(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* v___x_718_, lean_object* v_lhs_719_, lean_object* v_rhs_720_, uint8_t v___x_721_, uint8_t v_a_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_toCold_728_; uint8_t v_trackZetaDelta_729_; lean_object* v_zetaDeltaSet_730_; lean_object* v_lctx_731_; lean_object* v_localInstances_732_; lean_object* v_defEqCtx_x3f_733_; lean_object* v_synthPendingDepth_734_; lean_object* v_customCanUnfoldPredicate_x3f_735_; uint8_t v_univApprox_736_; uint8_t v_inTypeClassResolution_737_; uint8_t v_cacheInferType_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_888_; 
v_toCold_728_ = lean_ctor_get(v___y_725_, 0);
lean_inc_ref(v_toCold_728_);
v_trackZetaDelta_729_ = lean_ctor_get_uint8(v___y_723_, sizeof(void*)*7);
v_zetaDeltaSet_730_ = lean_ctor_get(v___y_723_, 1);
v_lctx_731_ = lean_ctor_get(v___y_723_, 2);
v_localInstances_732_ = lean_ctor_get(v___y_723_, 3);
v_defEqCtx_x3f_733_ = lean_ctor_get(v___y_723_, 4);
v_synthPendingDepth_734_ = lean_ctor_get(v___y_723_, 5);
v_customCanUnfoldPredicate_x3f_735_ = lean_ctor_get(v___y_723_, 6);
v_univApprox_736_ = lean_ctor_get_uint8(v___y_723_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_737_ = lean_ctor_get_uint8(v___y_723_, sizeof(void*)*7 + 2);
v_cacheInferType_738_ = lean_ctor_get_uint8(v___y_723_, sizeof(void*)*7 + 3);
v_isSharedCheck_888_ = !lean_is_exclusive(v___y_723_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v___y_723_, 0);
lean_dec(v_unused_889_);
v___x_740_ = v___y_723_;
v_isShared_741_ = v_isSharedCheck_888_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_735_);
lean_inc(v_synthPendingDepth_734_);
lean_inc(v_defEqCtx_x3f_733_);
lean_inc(v_localInstances_732_);
lean_inc(v_lctx_731_);
lean_inc(v_zetaDeltaSet_730_);
lean_dec(v___y_723_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_888_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_currRecDepth_742_; lean_object* v_ref_743_; uint8_t v_suppressElabErrors_744_; uint8_t v_isRecordingDeps_745_; lean_object* v_fileName_746_; lean_object* v_fileMap_747_; lean_object* v_options_748_; lean_object* v_currNamespace_749_; lean_object* v_openDecls_750_; lean_object* v_initHeartbeats_751_; lean_object* v_maxHeartbeats_752_; lean_object* v_quotContext_753_; lean_object* v_currMacroScope_754_; lean_object* v_cancelTk_x3f_755_; lean_object* v_inheritedTraceOptions_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_886_; 
v_currRecDepth_742_ = lean_ctor_get(v___y_725_, 1);
v_ref_743_ = lean_ctor_get(v___y_725_, 2);
v_suppressElabErrors_744_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*3 + 2);
v_isRecordingDeps_745_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*3 + 3);
v_fileName_746_ = lean_ctor_get(v_toCold_728_, 0);
v_fileMap_747_ = lean_ctor_get(v_toCold_728_, 1);
v_options_748_ = lean_ctor_get(v_toCold_728_, 2);
v_currNamespace_749_ = lean_ctor_get(v_toCold_728_, 4);
v_openDecls_750_ = lean_ctor_get(v_toCold_728_, 5);
v_initHeartbeats_751_ = lean_ctor_get(v_toCold_728_, 6);
v_maxHeartbeats_752_ = lean_ctor_get(v_toCold_728_, 7);
v_quotContext_753_ = lean_ctor_get(v_toCold_728_, 8);
v_currMacroScope_754_ = lean_ctor_get(v_toCold_728_, 9);
v_cancelTk_x3f_755_ = lean_ctor_get(v_toCold_728_, 10);
v_inheritedTraceOptions_756_ = lean_ctor_get(v_toCold_728_, 11);
v_isSharedCheck_886_ = !lean_is_exclusive(v_toCold_728_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_toCold_728_, 3);
lean_dec(v_unused_887_);
v___x_758_ = v_toCold_728_;
v_isShared_759_ = v_isSharedCheck_886_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_inheritedTraceOptions_756_);
lean_inc(v_cancelTk_x3f_755_);
lean_inc(v_currMacroScope_754_);
lean_inc(v_quotContext_753_);
lean_inc(v_maxHeartbeats_752_);
lean_inc(v_initHeartbeats_751_);
lean_inc(v_openDecls_750_);
lean_inc(v_currNamespace_749_);
lean_inc(v_options_748_);
lean_inc(v_fileMap_747_);
lean_inc(v_fileName_746_);
lean_dec(v_toCold_728_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_886_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint64_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_718_);
v___x_761_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_761_, 0, v___x_718_);
lean_ctor_set_uint64(v___x_761_, sizeof(void*)*1, v___x_760_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_761_);
v___x_763_ = v___x_740_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_zetaDeltaSet_730_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_lctx_731_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_localInstances_732_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_defEqCtx_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_885_, 5, v_synthPendingDepth_734_);
lean_ctor_set(v_reuseFailAlloc_885_, 6, v_customCanUnfoldPredicate_x3f_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*7, v_trackZetaDelta_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*7 + 1, v_univApprox_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*7 + 2, v_inTypeClassResolution_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*7 + 3, v_cacheInferType_738_);
v___x_763_ = v_reuseFailAlloc_885_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
uint16_t v___y_765_; lean_object* v___y_766_; lean_object* v_fileName_767_; lean_object* v_fileMap_768_; lean_object* v_currNamespace_769_; lean_object* v_openDecls_770_; lean_object* v_initHeartbeats_771_; lean_object* v_maxHeartbeats_772_; lean_object* v_quotContext_773_; lean_object* v_currMacroScope_774_; lean_object* v_cancelTk_x3f_775_; lean_object* v_inheritedTraceOptions_776_; lean_object* v_currRecDepth_777_; lean_object* v_ref_778_; uint8_t v_suppressElabErrors_779_; uint8_t v_isRecordingDeps_780_; lean_object* v___y_781_; uint16_t v___y_848_; uint8_t v___y_849_; lean_object* v___y_850_; lean_object* v___y_873_; 
if (v_isRecordingDeps_745_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Lean_Meta_smartUnfolding;
v___x_883_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_748_, v___x_882_, v_a_722_);
v___y_873_ = v___x_883_;
goto v___jp_872_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_748_);
v___y_873_ = v___x_884_;
goto v___jp_872_;
}
v___jp_764_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = l_Lean_maxRecDepth;
v___x_783_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v___y_766_, v___x_782_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 11, v_inheritedTraceOptions_776_);
lean_ctor_set(v___x_758_, 10, v_cancelTk_x3f_775_);
lean_ctor_set(v___x_758_, 9, v_currMacroScope_774_);
lean_ctor_set(v___x_758_, 8, v_quotContext_773_);
lean_ctor_set(v___x_758_, 7, v_maxHeartbeats_772_);
lean_ctor_set(v___x_758_, 6, v_initHeartbeats_771_);
lean_ctor_set(v___x_758_, 5, v_openDecls_770_);
lean_ctor_set(v___x_758_, 4, v_currNamespace_769_);
lean_ctor_set(v___x_758_, 3, v___x_783_);
lean_ctor_set(v___x_758_, 2, v___y_766_);
lean_ctor_set(v___x_758_, 1, v_fileMap_768_);
lean_ctor_set(v___x_758_, 0, v_fileName_767_);
v___x_785_ = v___x_758_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_fileName_767_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_fileMap_768_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v___y_766_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_currNamespace_769_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_openDecls_770_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v_initHeartbeats_771_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_maxHeartbeats_772_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v_quotContext_773_);
lean_ctor_set(v_reuseFailAlloc_846_, 9, v_currMacroScope_774_);
lean_ctor_set(v_reuseFailAlloc_846_, 10, v_cancelTk_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_846_, 11, v_inheritedTraceOptions_776_);
v___x_785_ = v_reuseFailAlloc_846_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_currRecDepth_777_);
lean_ctor_set(v___x_786_, 2, v_ref_778_);
lean_ctor_set_uint16(v___x_786_, sizeof(void*)*3, v___y_765_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*3 + 2, v_suppressElabErrors_779_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*3 + 3, v_isRecordingDeps_780_);
v___x_787_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_lhs_719_, v_rhs_720_, v___x_763_, v___y_724_, v___x_786_, v___y_781_);
lean_dec_ref_known(v___x_786_, 3);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_837_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_837_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_837_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_837_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_836_; 
v_fst_792_ = lean_ctor_get(v_a_788_, 0);
v_snd_793_ = lean_ctor_get(v_a_788_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_788_);
if (v_isSharedCheck_836_ == 0)
{
v___x_795_ = v_a_788_;
v_isShared_796_ = v_isSharedCheck_836_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_a_788_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_836_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__1, &l_Lean_validateDefEqAttr___lam__0___closed__1_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__1);
lean_inc(v_fst_792_);
v___x_798_ = l_Lean_indentExpr(v_fst_792_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v___x_798_);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_835_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_env_806_; uint8_t v_isExporting_807_; 
v___x_801_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__3, &l_Lean_validateDefEqAttr___lam__0___closed__3_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__3);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
lean_inc(v_snd_793_);
v___x_803_ = l_Lean_indentExpr(v_snd_793_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_st_ref_get(v___y_726_);
v_env_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_env_806_);
lean_dec(v___x_805_);
v_isExporting_807_ = lean_ctor_get_uint8(v_env_806_, sizeof(void*)*8);
lean_dec_ref(v_env_806_);
if (v_isExporting_807_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v___y_725_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_804_);
v___x_809_ = v___x_790_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_del_object(v___x_790_);
v___x_811_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed), 7, 2);
lean_closure_set(v___x_811_, 0, v_fst_792_);
lean_closure_set(v___x_811_, 1, v_snd_793_);
v___x_812_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___x_811_, v___x_721_, v___x_763_, v___y_724_, v___y_725_, v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_826_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_826_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; 
v___x_817_ = lean_unbox(v_a_813_);
lean_dec(v_a_813_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_804_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_804_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_821_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__6, &l_Lean_validateDefEqAttr___lam__0___closed__6_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__6);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_822_);
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref_known(v___x_804_, 2);
v_a_827_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_812_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_812_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
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
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v___y_725_);
v_a_838_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_787_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_787_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
v___jp_847_:
{
lean_object* v___x_851_; lean_object* v_env_852_; lean_object* v_nextMacroScope_853_; lean_object* v_ngen_854_; lean_object* v_auxDeclNGen_855_; lean_object* v_traceState_856_; lean_object* v_recordedDeps_857_; lean_object* v_messages_858_; lean_object* v_infoState_859_; lean_object* v_snapshotTasks_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_870_; 
v___x_851_ = lean_st_ref_take(v___y_726_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
v_nextMacroScope_853_ = lean_ctor_get(v___x_851_, 1);
v_ngen_854_ = lean_ctor_get(v___x_851_, 2);
v_auxDeclNGen_855_ = lean_ctor_get(v___x_851_, 3);
v_traceState_856_ = lean_ctor_get(v___x_851_, 4);
v_recordedDeps_857_ = lean_ctor_get(v___x_851_, 6);
v_messages_858_ = lean_ctor_get(v___x_851_, 7);
v_infoState_859_ = lean_ctor_get(v___x_851_, 8);
v_snapshotTasks_860_ = lean_ctor_get(v___x_851_, 9);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_851_, 5);
lean_dec(v_unused_871_);
v___x_862_ = v___x_851_;
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snapshotTasks_860_);
lean_inc(v_infoState_859_);
lean_inc(v_messages_858_);
lean_inc(v_recordedDeps_857_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_855_);
lean_inc(v_ngen_854_);
lean_inc(v_nextMacroScope_853_);
lean_inc(v_env_852_);
lean_dec(v___x_851_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_864_ = l_Lean_Kernel_enableDiag(v_env_852_, v___y_849_);
v___x_865_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 5, v___x_865_);
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_867_ = v___x_862_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_nextMacroScope_853_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_ngen_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_auxDeclNGen_855_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_traceState_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 6, v_recordedDeps_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 7, v_messages_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 8, v_infoState_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 9, v_snapshotTasks_860_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = lean_st_ref_put(v___y_726_, v___x_867_);
lean_inc(v_ref_743_);
lean_inc(v_currRecDepth_742_);
v___y_765_ = v___y_848_;
v___y_766_ = v___y_850_;
v_fileName_767_ = v_fileName_746_;
v_fileMap_768_ = v_fileMap_747_;
v_currNamespace_769_ = v_currNamespace_749_;
v_openDecls_770_ = v_openDecls_750_;
v_initHeartbeats_771_ = v_initHeartbeats_751_;
v_maxHeartbeats_772_ = v_maxHeartbeats_752_;
v_quotContext_773_ = v_quotContext_753_;
v_currMacroScope_774_ = v_currMacroScope_754_;
v_cancelTk_x3f_775_ = v_cancelTk_x3f_755_;
v_inheritedTraceOptions_776_ = v_inheritedTraceOptions_756_;
v_currRecDepth_777_ = v_currRecDepth_742_;
v_ref_778_ = v_ref_743_;
v_suppressElabErrors_779_ = v_suppressElabErrors_744_;
v_isRecordingDeps_780_ = v_isRecordingDeps_745_;
v___y_781_ = v___y_726_;
goto v___jp_764_;
}
}
}
v___jp_872_:
{
uint16_t v___x_874_; lean_object* v___x_875_; lean_object* v_env_876_; uint8_t v___x_877_; uint16_t v___x_878_; uint16_t v___x_879_; uint16_t v___x_880_; uint8_t v___x_881_; 
v___x_874_ = l_Lean_OptionFlags_ofOptions(v___y_873_);
v___x_875_ = lean_st_ref_get(v___y_726_);
v_env_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc_ref(v_env_876_);
lean_dec(v___x_875_);
v___x_877_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_876_);
lean_dec_ref(v_env_876_);
v___x_878_ = 512;
v___x_879_ = lean_uint16_land(v___x_874_, v___x_878_);
v___x_880_ = 0;
v___x_881_ = lean_uint16_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
if (v___x_877_ == 0)
{
v___y_848_ = v___x_874_;
v___y_849_ = v___x_721_;
v___y_850_ = v___y_873_;
goto v___jp_847_;
}
else
{
lean_inc(v_ref_743_);
lean_inc(v_currRecDepth_742_);
v___y_765_ = v___x_874_;
v___y_766_ = v___y_873_;
v_fileName_767_ = v_fileName_746_;
v_fileMap_768_ = v_fileMap_747_;
v_currNamespace_769_ = v_currNamespace_749_;
v_openDecls_770_ = v_openDecls_750_;
v_initHeartbeats_771_ = v_initHeartbeats_751_;
v_maxHeartbeats_772_ = v_maxHeartbeats_752_;
v_quotContext_773_ = v_quotContext_753_;
v_currMacroScope_774_ = v_currMacroScope_754_;
v_cancelTk_x3f_775_ = v_cancelTk_x3f_755_;
v_inheritedTraceOptions_776_ = v_inheritedTraceOptions_756_;
v_currRecDepth_777_ = v_currRecDepth_742_;
v_ref_778_ = v_ref_743_;
v_suppressElabErrors_779_ = v_suppressElabErrors_744_;
v_isRecordingDeps_780_ = v_isRecordingDeps_745_;
v___y_781_ = v___y_726_;
goto v___jp_764_;
}
}
else
{
if (v___x_877_ == 0)
{
lean_inc(v_ref_743_);
lean_inc(v_currRecDepth_742_);
v___y_765_ = v___x_874_;
v___y_766_ = v___y_873_;
v_fileName_767_ = v_fileName_746_;
v_fileMap_768_ = v_fileMap_747_;
v_currNamespace_769_ = v_currNamespace_749_;
v_openDecls_770_ = v_openDecls_750_;
v_initHeartbeats_771_ = v_initHeartbeats_751_;
v_maxHeartbeats_772_ = v_maxHeartbeats_752_;
v_quotContext_773_ = v_quotContext_753_;
v_currMacroScope_774_ = v_currMacroScope_754_;
v_cancelTk_x3f_775_ = v_cancelTk_x3f_755_;
v_inheritedTraceOptions_776_ = v_inheritedTraceOptions_756_;
v_currRecDepth_777_ = v_currRecDepth_742_;
v_ref_778_ = v_ref_743_;
v_suppressElabErrors_779_ = v_suppressElabErrors_744_;
v_isRecordingDeps_780_ = v_isRecordingDeps_745_;
v___y_781_ = v___y_726_;
goto v___jp_764_;
}
else
{
v___y_848_ = v___x_874_;
v___y_849_ = v_a_722_;
v___y_850_ = v___y_873_;
goto v___jp_847_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object* v___x_890_, lean_object* v_lhs_891_, lean_object* v_rhs_892_, lean_object* v___x_893_, lean_object* v_a_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v___x_8740__boxed_900_; uint8_t v_a_8741__boxed_901_; lean_object* v_res_902_; 
v___x_8740__boxed_900_ = lean_unbox(v___x_893_);
v_a_8741__boxed_901_ = lean_unbox(v_a_894_);
v_res_902_ = l_Lean_validateDefEqAttr___lam__0(v___x_890_, v_lhs_891_, v_rhs_892_, v___x_8740__boxed_900_, v_a_8741__boxed_901_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* v_lhs_903_, lean_object* v_rhs_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
lean_inc_ref(v_rhs_904_);
lean_inc_ref(v_lhs_903_);
v___x_910_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_lhs_903_, v_rhs_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_930_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_930_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_930_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_930_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; 
v___x_915_ = lean_unbox(v_a_911_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_del_object(v___x_913_);
v___x_916_ = 1;
v___x_917_ = l_Lean_Meta_Context_config(v___y_905_);
v___x_918_ = lean_box(v___x_916_);
lean_inc_ref(v_rhs_904_);
lean_inc_ref(v_lhs_903_);
v___f_919_ = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0___boxed), 10, 5);
lean_closure_set(v___f_919_, 0, v___x_917_);
lean_closure_set(v___f_919_, 1, v_lhs_903_);
lean_closure_set(v___f_919_, 2, v_rhs_904_);
lean_closure_set(v___f_919_, 3, v___x_918_);
lean_closure_set(v___f_919_, 4, v_a_911_);
v___x_920_ = lean_unsigned_to_nat(2u);
v___x_921_ = lean_mk_empty_array_with_capacity(v___x_920_);
v___x_922_ = lean_array_push(v___x_921_, v_lhs_903_);
v___x_923_ = lean_array_push(v___x_922_, v_rhs_904_);
v___x_924_ = l_Lean_MessageData_ofLazyM(v___f_919_, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_924_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v_a_911_);
lean_dec_ref(v_rhs_904_);
lean_dec_ref(v_lhs_903_);
v___x_926_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_926_);
v___x_928_ = v___x_913_;
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
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_rhs_904_);
lean_dec_ref(v_lhs_903_);
v_a_931_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_910_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_910_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* v_lhs_939_, lean_object* v_rhs_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_939_, v_rhs_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_ctor_set(v___x_951_, 3, v___x_950_);
lean_ctor_set(v___x_951_, 4, v___x_949_);
lean_ctor_set(v___x_951_, 5, v___x_949_);
lean_ctor_set(v___x_951_, 6, v___x_949_);
lean_ctor_set(v___x_951_, 7, v___x_949_);
lean_ctor_set(v___x_951_, 8, v___x_949_);
lean_ctor_set(v___x_951_, 9, v___x_949_);
lean_ctor_set(v___x_951_, 10, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_unsigned_to_nat(32u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((size_t)5ULL);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_unsigned_to_nat(32u);
v___x_958_ = lean_mk_empty_array_with_capacity(v___x_957_);
v___x_959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
lean_ctor_set(v___x_960_, 2, v___x_956_);
lean_ctor_set(v___x_960_, 3, v___x_956_);
lean_ctor_set_usize(v___x_960_, 4, v___x_955_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = lean_box(1);
v___x_962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
lean_ctor_set(v___x_964_, 2, v___x_961_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_986_, lean_object* v_declHint_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_env_992_; uint8_t v___x_993_; 
v___x_990_ = lean_box(0);
v___x_991_ = lean_st_ref_get(v___y_988_);
v_env_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc_ref(v_env_992_);
lean_dec(v___x_991_);
v___x_993_ = l_Lean_Name_isAnonymous(v_declHint_987_);
if (v___x_993_ == 0)
{
uint8_t v_isExporting_994_; 
v_isExporting_994_ = lean_ctor_get_uint8(v_env_992_, sizeof(void*)*8);
if (v_isExporting_994_ == 0)
{
lean_object* v___x_995_; 
lean_dec_ref(v_env_992_);
lean_dec(v_declHint_987_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v_msg_986_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
lean_inc_ref(v_env_992_);
v___x_996_ = l_Lean_Environment_setExporting(v_env_992_, v___x_993_);
lean_inc(v_declHint_987_);
lean_inc_ref(v___x_996_);
v___x_997_ = l_Lean_Environment_contains(v___x_996_, v_declHint_987_, v_isExporting_994_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v___x_996_);
lean_dec_ref(v_env_992_);
lean_dec(v_declHint_987_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_msg_986_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_c_1004_; lean_object* v___x_1005_; 
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1001_ = l_Lean_Options_empty;
v___x_1002_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1002_, 0, v___x_996_);
lean_ctor_set(v___x_1002_, 1, v___x_999_);
lean_ctor_set(v___x_1002_, 2, v___x_1000_);
lean_ctor_set(v___x_1002_, 3, v___x_1001_);
lean_inc(v_declHint_987_);
v___x_1003_ = l_Lean_MessageData_ofConstName(v_declHint_987_, v___x_993_);
v_c_1004_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1004_, 0, v___x_1002_);
lean_ctor_set(v_c_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_992_, v_declHint_987_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v_env_992_);
lean_dec(v_declHint_987_);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_c_1004_);
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_MessageData_note(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_msg_986_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1047_; 
v_val_1013_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1015_ = v___x_1005_;
v_isShared_1016_ = v_isSharedCheck_1047_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v___x_1005_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1047_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_mod_1019_; uint8_t v___x_1020_; 
v___x_1017_ = l_Lean_Environment_header(v_env_992_);
lean_dec_ref(v_env_992_);
v___x_1018_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1017_);
v_mod_1019_ = lean_array_get(v___x_990_, v___x_1018_, v_val_1013_);
lean_dec(v_val_1013_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Lean_isPrivateName(v_declHint_987_);
lean_dec(v_declHint_987_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_c_1004_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_ofName(v_mod_1019_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_note(v___x_1028_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_msg_986_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1030_);
v___x_1032_ = v___x_1015_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_c_1004_);
v___x_1036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_ofName(v_mod_1019_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_MessageData_note(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_msg_986_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1043_);
v___x_1045_ = v___x_1015_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_env_992_);
lean_dec(v_declHint_987_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_msg_986_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1049_, lean_object* v_declHint_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1049_, v_declHint_1050_, v___y_1051_);
lean_dec(v___y_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1054_, lean_object* v_declHint_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1069_; 
v___x_1059_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1054_, v_declHint_1055_, v___y_1057_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1069_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = l_Lean_unknownIdentifierMessageTag;
v___x_1065_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1070_, lean_object* v_declHint_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1070_, v_declHint_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v_toCold_1081_; lean_object* v_env_1082_; lean_object* v_options_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1080_ = lean_st_ref_get(v___y_1078_);
v_toCold_1081_ = lean_ctor_get(v___y_1077_, 0);
v_env_1082_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1080_);
v_options_1083_ = lean_ctor_get(v_toCold_1081_, 2);
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1085_ = lean_unsigned_to_nat(32u);
v___x_1086_ = lean_mk_empty_array_with_capacity(v___x_1085_);
lean_dec_ref(v___x_1086_);
v___x_1087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
lean_inc_ref(v_options_1083_);
v___x_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1088_, 0, v_env_1082_);
lean_ctor_set(v___x_1088_, 1, v___x_1084_);
lean_ctor_set(v___x_1088_, 2, v___x_1087_);
lean_ctor_set(v___x_1088_, 3, v_options_1083_);
v___x_1089_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_msgData_1076_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_ref_1100_; lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_ref_1100_ = lean_ctor_get(v___y_1097_, 2);
v___x_1101_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_1096_, v___y_1097_, v___y_1098_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_inc(v_ref_1100_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_ref_1100_);
lean_ctor_set(v___x_1106_, 1, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1116_, lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_toCold_1121_; lean_object* v_currRecDepth_1122_; lean_object* v_ref_1123_; uint16_t v_optionFlags_1124_; uint8_t v_suppressElabErrors_1125_; uint8_t v_isRecordingDeps_1126_; lean_object* v_ref_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_toCold_1121_ = lean_ctor_get(v___y_1118_, 0);
v_currRecDepth_1122_ = lean_ctor_get(v___y_1118_, 1);
v_ref_1123_ = lean_ctor_get(v___y_1118_, 2);
v_optionFlags_1124_ = lean_ctor_get_uint16(v___y_1118_, sizeof(void*)*3);
v_suppressElabErrors_1125_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1126_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*3 + 3);
v_ref_1127_ = l_Lean_replaceRef(v_ref_1116_, v_ref_1123_);
lean_inc(v_currRecDepth_1122_);
lean_inc_ref(v_toCold_1121_);
v___x_1128_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1128_, 0, v_toCold_1121_);
lean_ctor_set(v___x_1128_, 1, v_currRecDepth_1122_);
lean_ctor_set(v___x_1128_, 2, v_ref_1127_);
lean_ctor_set_uint16(v___x_1128_, sizeof(void*)*3, v_optionFlags_1124_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*3 + 2, v_suppressElabErrors_1125_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*3 + 3, v_isRecordingDeps_1126_);
v___x_1129_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1117_, v___x_1128_, v___y_1119_);
lean_dec_ref_known(v___x_1128_, 3);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1130_, lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1130_, v_msg_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_ref_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1136_, lean_object* v_msg_1137_, lean_object* v_declHint_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v_a_1143_; lean_object* v___x_1144_; 
v___x_1142_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1137_, v_declHint_1138_, v___y_1139_, v___y_1140_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1136_, v_a_1143_, v___y_1139_, v___y_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1145_, lean_object* v_msg_1146_, lean_object* v_declHint_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1145_, v_msg_1146_, v_declHint_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v_ref_1145_);
return v_res_1151_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1158_, lean_object* v_constName_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1163_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1164_ = 0;
lean_inc(v_constName_1159_);
v___x_1165_ = l_Lean_MessageData_ofConstName(v_constName_1159_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1163_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1158_, v___x_1168_, v_constName_1159_, v___y_1160_, v___y_1161_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1170_, lean_object* v_constName_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1170_, v_constName_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_ref_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object* v_constName_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_ref_1180_; lean_object* v___x_1181_; 
v_ref_1180_ = lean_ctor_get(v___y_1177_, 2);
v___x_1181_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1180_, v_constName_1176_, v___y_1177_, v___y_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object* v_constName_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = lean_st_ref_get(v___y_1189_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = 0;
lean_inc(v_constName_1187_);
v___x_1194_ = l_Lean_Environment_findConstVal_x3f(v_env_1192_, v_constName_1187_, v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1187_, v___y_1188_, v___y_1189_);
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_constName_1187_);
v_val_1196_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1194_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_dec(v___x_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 0);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object* v_constName_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1208_;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__2(void){
_start:
{
lean_object* v___x_1216_; uint64_t v___x_1217_; 
v___x_1216_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__1));
v___x_1217_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3(void){
_start:
{
uint64_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_uint64_once(&l_Lean_validateDefEqAttr___closed__2, &l_Lean_validateDefEqAttr___closed__2_once, _init_l_Lean_validateDefEqAttr___closed__2);
v___x_1219_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__1));
v___x_1220_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set_uint64(v___x_1220_, sizeof(void*)*1, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_box(1);
v___x_1224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1225_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
lean_ctor_set(v___x_1226_, 2, v___x_1223_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7(void){
_start:
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1229_ = 1;
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_box(0);
v___x_1232_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__6));
v___x_1233_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__5, &l_Lean_validateDefEqAttr___closed__5_once, _init_l_Lean_validateDefEqAttr___closed__5);
v___x_1234_ = lean_box(1);
v___x_1235_ = 0;
v___x_1236_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__3, &l_Lean_validateDefEqAttr___closed__3_once, _init_l_Lean_validateDefEqAttr___closed__3);
v___x_1237_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1234_);
lean_ctor_set(v___x_1237_, 2, v___x_1233_);
lean_ctor_set(v___x_1237_, 3, v___x_1232_);
lean_ctor_set(v___x_1237_, 4, v___x_1231_);
lean_ctor_set(v___x_1237_, 5, v___x_1230_);
lean_ctor_set(v___x_1237_, 6, v___x_1231_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*7, v___x_1235_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*7 + 1, v___x_1235_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*7 + 2, v___x_1235_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*7 + 3, v___x_1229_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
lean_ctor_set(v___x_1240_, 3, v___x_1239_);
lean_ctor_set(v___x_1240_, 4, v___x_1238_);
lean_ctor_set(v___x_1240_, 5, v___x_1238_);
lean_ctor_set(v___x_1240_, 6, v___x_1238_);
lean_ctor_set(v___x_1240_, 7, v___x_1238_);
lean_ctor_set(v___x_1240_, 8, v___x_1238_);
lean_ctor_set(v___x_1240_, 9, v___x_1238_);
lean_ctor_set(v___x_1240_, 10, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
lean_ctor_set(v___x_1242_, 3, v___x_1241_);
lean_ctor_set(v___x_1242_, 4, v___x_1241_);
lean_ctor_set(v___x_1242_, 5, v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_ctor_set(v___x_1244_, 2, v___x_1243_);
lean_ctor_set(v___x_1244_, 3, v___x_1243_);
lean_ctor_set(v___x_1244_, 4, v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1245_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__10, &l_Lean_validateDefEqAttr___closed__10_once, _init_l_Lean_validateDefEqAttr___closed__10);
v___x_1246_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1247_ = lean_box(1);
v___x_1248_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__9, &l_Lean_validateDefEqAttr___closed__9_once, _init_l_Lean_validateDefEqAttr___closed__9);
v___x_1249_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__8, &l_Lean_validateDefEqAttr___closed__8_once, _init_l_Lean_validateDefEqAttr___closed__8);
v___x_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
lean_ctor_set(v___x_1250_, 2, v___x_1247_);
lean_ctor_set(v___x_1250_, 3, v___x_1246_);
lean_ctor_set(v___x_1250_, 4, v___x_1245_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object* v_declName_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___f_1255_; lean_object* v___x_1256_; 
v___f_1255_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1256_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_declName_1251_, v_a_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_type_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v_type_1258_ = lean_ctor_get(v_a_1257_, 2);
lean_inc_ref(v_type_1258_);
lean_dec(v_a_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__7, &l_Lean_validateDefEqAttr___closed__7_once, _init_l_Lean_validateDefEqAttr___closed__7);
v___x_1260_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__11, &l_Lean_validateDefEqAttr___closed__11_once, _init_l_Lean_validateDefEqAttr___closed__11);
v___x_1261_ = lean_st_mk_ref(v___x_1260_);
v___x_1262_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_1258_, v___f_1255_, v___x_1259_, v___x_1261_, v_a_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_st_ref_get(v___x_1261_);
lean_dec(v___x_1261_);
lean_dec(v___x_1267_);
if (v_isShared_1266_ == 0)
{
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1263_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_dec(v___x_1261_);
return v___x_1262_;
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_a_1272_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1256_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1256_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object* v_declName_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_validateDefEqAttr(v_declName_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_1285_, lean_object* v_x_1286_, uint8_t v_isExporting_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_1286_, v_isExporting_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v_isExporting_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_isExporting_boxed_1302_; lean_object* v_res_1303_; 
v_isExporting_boxed_1302_ = lean_unbox(v_isExporting_1296_);
v_res_1303_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_1294_, v_x_1295_, v_isExporting_boxed_1302_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object* v_00_u03b1_1304_, lean_object* v_x_1305_, uint8_t v_when_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_1305_, v_when_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_x_1314_, lean_object* v_when_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_when_boxed_1321_; lean_object* v_res_1322_; 
v_when_boxed_1321_ = lean_unbox(v_when_1315_);
v_res_1322_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(v_00_u03b1_1313_, v_x_1314_, v_when_boxed_1321_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object* v_00_u03b1_1323_, lean_object* v_constName_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1324_, v___y_1325_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_constName_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_1329_, v_constName_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1335_, lean_object* v_ref_1336_, lean_object* v_constName_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1336_, v_constName_1337_, v___y_1338_, v___y_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_ref_1343_, lean_object* v_constName_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_1342_, v_ref_1343_, v_constName_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v_ref_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1349_, lean_object* v_ref_1350_, lean_object* v_msg_1351_, lean_object* v_declHint_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1350_, v_msg_1351_, v_declHint_1352_, v___y_1353_, v___y_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_ref_1358_, lean_object* v_msg_1359_, lean_object* v_declHint_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1357_, v_ref_1358_, v_msg_1359_, v_declHint_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v_ref_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1365_, lean_object* v_declHint_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1365_, v_declHint_1366_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1371_, lean_object* v_declHint_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1371_, v_declHint_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1377_, lean_object* v_ref_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1378_, v_msg_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_ref_1385_, lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1384_, v_ref_1385_, v_msg_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_ref_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1391_, lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1397_, v_msg_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1416_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1417_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1418_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1419_ = 0;
v___x_1420_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1421_ = l_Lean_registerTagAttribute(v___x_1415_, v___x_1416_, v___x_1417_, v___x_1418_, v___x_1419_, v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1(){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1427_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0));
v___x_1428_ = l_Lean_addBuiltinDocString(v___x_1426_, v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1458_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6));
v___x_1459_ = l_Lean_addBuiltinDeclarationRanges(v___x_1457_, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
return v_res_1461_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2));
v___x_1467_ = l_Lean_stringToMessageData(v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4));
v___x_1470_ = l_Lean_stringToMessageData(v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_attrName_1474_, lean_object* v_declName_1475_, lean_object* v_asyncPrefix_x3f_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___y_1481_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1476_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_MessageData_nil;
v___y_1481_ = v___x_1494_;
goto v___jp_1480_;
}
else
{
lean_object* v_val_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_val_1495_ = lean_ctor_get(v_asyncPrefix_x3f_1476_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_asyncPrefix_x3f_1476_, 1);
v___x_1496_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1497_ = l_Lean_MessageData_ofName(v_val_1495_);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___y_1481_ = v___x_1500_;
goto v___jp_1480_;
}
v___jp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1482_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1483_ = l_Lean_MessageData_ofName(v_attrName_1474_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = 0;
v___x_1488_ = l_Lean_MessageData_ofConstName(v_declName_1475_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1486_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___y_1481_);
v___x_1493_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1492_, v___y_1477_, v___y_1478_);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1501_, lean_object* v_declName_1502_, lean_object* v_asyncPrefix_x3f_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1501_, v_declName_1502_, v_asyncPrefix_x3f_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1507_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_attrName_1511_, lean_object* v_declName_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1516_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1517_ = l_Lean_MessageData_ofName(v_attrName_1511_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = 0;
v___x_1522_ = l_Lean_MessageData_ofConstName(v_declName_1512_, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1525_, v___y_1513_, v___y_1514_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1527_, lean_object* v_declName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1527_, v_declName_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object* v_attr_1533_, lean_object* v_decl_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___y_1539_; lean_object* v___x_1566_; lean_object* v_env_1567_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___x_1580_; 
v___x_1566_ = lean_st_ref_get(v___y_1536_);
v_env_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_env_1567_);
lean_dec(v___x_1566_);
v___x_1580_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1567_, v_decl_1534_);
if (lean_obj_tag(v___x_1580_) == 0)
{
v___y_1569_ = v___y_1535_;
v___y_1570_ = v___y_1536_;
goto v___jp_1568_;
}
else
{
lean_object* v_attr_1581_; lean_object* v_toAttributeImplCore_1582_; lean_object* v_name_1583_; lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1580_, 1);
lean_dec_ref(v_env_1567_);
v_attr_1581_ = lean_ctor_get(v_attr_1533_, 0);
lean_inc_ref(v_attr_1581_);
lean_dec_ref(v_attr_1533_);
v_toAttributeImplCore_1582_ = lean_ctor_get(v_attr_1581_, 0);
lean_inc_ref(v_toAttributeImplCore_1582_);
lean_dec_ref(v_attr_1581_);
v_name_1583_ = lean_ctor_get(v_toAttributeImplCore_1582_, 1);
lean_inc(v_name_1583_);
lean_dec_ref(v_toAttributeImplCore_1582_);
v___x_1584_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_1583_, v_decl_1534_, v___y_1535_, v___y_1536_);
return v___x_1584_;
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v_ext_1541_; lean_object* v_toEnvExtension_1542_; lean_object* v_env_1543_; lean_object* v_nextMacroScope_1544_; lean_object* v_ngen_1545_; lean_object* v_auxDeclNGen_1546_; lean_object* v_traceState_1547_; lean_object* v_recordedDeps_1548_; lean_object* v_messages_1549_; lean_object* v_infoState_1550_; lean_object* v_snapshotTasks_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1564_; 
v___x_1540_ = lean_st_ref_take(v___y_1539_);
v_ext_1541_ = lean_ctor_get(v_attr_1533_, 1);
lean_inc_ref(v_ext_1541_);
lean_dec_ref(v_attr_1533_);
v_toEnvExtension_1542_ = lean_ctor_get(v_ext_1541_, 0);
v_env_1543_ = lean_ctor_get(v___x_1540_, 0);
v_nextMacroScope_1544_ = lean_ctor_get(v___x_1540_, 1);
v_ngen_1545_ = lean_ctor_get(v___x_1540_, 2);
v_auxDeclNGen_1546_ = lean_ctor_get(v___x_1540_, 3);
v_traceState_1547_ = lean_ctor_get(v___x_1540_, 4);
v_recordedDeps_1548_ = lean_ctor_get(v___x_1540_, 6);
v_messages_1549_ = lean_ctor_get(v___x_1540_, 7);
v_infoState_1550_ = lean_ctor_get(v___x_1540_, 8);
v_snapshotTasks_1551_ = lean_ctor_get(v___x_1540_, 9);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v___x_1540_, 5);
lean_dec(v_unused_1565_);
v___x_1553_ = v___x_1540_;
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snapshotTasks_1551_);
lean_inc(v_infoState_1550_);
lean_inc(v_messages_1549_);
lean_inc(v_recordedDeps_1548_);
lean_inc(v_traceState_1547_);
lean_inc(v_auxDeclNGen_1546_);
lean_inc(v_ngen_1545_);
lean_inc(v_nextMacroScope_1544_);
lean_inc(v_env_1543_);
lean_dec(v___x_1540_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_asyncMode_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v_asyncMode_1555_ = lean_ctor_get(v_toEnvExtension_1542_, 2);
lean_inc(v_asyncMode_1555_);
v___x_1556_ = lean_box(0);
lean_inc(v_decl_1534_);
v___x_1557_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1541_, v_env_1543_, v_decl_1534_, v_asyncMode_1555_, v_decl_1534_);
lean_dec(v_asyncMode_1555_);
v___x_1558_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 5, v___x_1558_);
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1560_ = v___x_1553_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_nextMacroScope_1544_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_ngen_1545_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_auxDeclNGen_1546_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_traceState_1547_);
lean_ctor_set(v_reuseFailAlloc_1563_, 5, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1563_, 6, v_recordedDeps_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 7, v_messages_1549_);
lean_ctor_set(v_reuseFailAlloc_1563_, 8, v_infoState_1550_);
lean_ctor_set(v_reuseFailAlloc_1563_, 9, v_snapshotTasks_1551_);
v___x_1560_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_st_ref_put(v___y_1539_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1556_);
return v___x_1562_;
}
}
}
v___jp_1568_:
{
lean_object* v_ext_1571_; lean_object* v_toEnvExtension_1572_; lean_object* v_attr_1573_; lean_object* v_asyncMode_1574_; uint8_t v___x_1575_; 
v_ext_1571_ = lean_ctor_get(v_attr_1533_, 1);
v_toEnvExtension_1572_ = lean_ctor_get(v_ext_1571_, 0);
v_attr_1573_ = lean_ctor_get(v_attr_1533_, 0);
v_asyncMode_1574_ = lean_ctor_get(v_toEnvExtension_1572_, 2);
lean_inc(v_decl_1534_);
lean_inc_ref(v_env_1567_);
v___x_1575_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1567_, v_decl_1534_, v_asyncMode_1574_);
if (v___x_1575_ == 0)
{
lean_object* v_toAttributeImplCore_1576_; lean_object* v_name_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_inc_ref(v_attr_1573_);
lean_dec_ref(v_attr_1533_);
v_toAttributeImplCore_1576_ = lean_ctor_get(v_attr_1573_, 0);
lean_inc_ref(v_toAttributeImplCore_1576_);
lean_dec_ref(v_attr_1573_);
v_name_1577_ = lean_ctor_get(v_toAttributeImplCore_1576_, 1);
lean_inc(v_name_1577_);
lean_dec_ref(v_toAttributeImplCore_1576_);
v___x_1578_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1567_);
v___x_1579_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_1577_, v_decl_1534_, v___x_1578_, v___y_1569_, v___y_1570_);
return v___x_1579_;
}
else
{
lean_dec_ref(v_env_1567_);
v___y_1539_ = v___y_1570_;
goto v___jp_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object* v_attr_1585_, lean_object* v_decl_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1585_, v_decl_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object* v_declName_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
lean_inc(v_declName_1591_);
v___x_1595_ = l_Lean_validateDefEqAttr(v_declName_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1595_, 1);
v___x_1596_ = l_Lean_backwardDefeqAttr;
v___x_1597_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v___x_1596_, v_declName_1591_, v___y_1592_, v___y_1593_);
return v___x_1597_;
}
else
{
lean_dec(v_declName_1591_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_declName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___f_1613_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1614_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1615_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1616_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1617_ = 0;
v___x_1618_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1619_ = l_Lean_registerTagAttribute(v___x_1614_, v___x_1615_, v___f_1613_, v___x_1616_, v___x_1617_, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1622_, lean_object* v_attrName_1623_, lean_object* v_declName_1624_, lean_object* v_asyncPrefix_x3f_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1623_, v_declName_1624_, v_asyncPrefix_x3f_1625_, v___y_1626_, v___y_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_attrName_1631_, lean_object* v_declName_1632_, lean_object* v_asyncPrefix_x3f_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1630_, v_attrName_1631_, v_declName_1632_, v_asyncPrefix_x3f_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_1638_, lean_object* v_attrName_1639_, lean_object* v_declName_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1639_, v_declName_1640_, v___y_1641_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_attrName_1646_, lean_object* v_declName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_1645_, v_attrName_1646_, v_declName_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1655_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0));
v___x_1656_ = l_Lean_addBuiltinDocString(v___x_1654_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1686_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6));
v___x_1687_ = l_Lean_addBuiltinDeclarationRanges(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* v_type_1701_, lean_object* v_proof_1702_, lean_object* v_a_1703_){
_start:
{
if (lean_obj_tag(v_type_1701_) == 7)
{
if (lean_obj_tag(v_proof_1702_) == 6)
{
lean_object* v_body_1705_; lean_object* v_body_1706_; 
v_body_1705_ = lean_ctor_get(v_type_1701_, 2);
v_body_1706_ = lean_ctor_get(v_proof_1702_, 2);
lean_inc_ref(v_body_1706_);
lean_dec_ref_known(v_proof_1702_, 3);
v_type_1701_ = v_body_1705_;
v_proof_1702_ = v_body_1706_;
goto _start;
}
else
{
uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec_ref(v_proof_1702_);
v___x_1708_ = 0;
v___x_1709_ = lean_box(v___x_1708_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_1712_ = lean_unsigned_to_nat(3u);
v___x_1713_ = l_Lean_Expr_isAppOfArity(v_type_1701_, v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_proof_1702_);
v___x_1714_ = lean_box(v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1));
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = l_Lean_Expr_isAppOfArity(v_proof_1702_, v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3));
v___x_1720_ = l_Lean_Expr_isAppOfArity(v_proof_1702_, v___x_1719_, v___x_1717_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5));
v___x_1722_ = lean_unsigned_to_nat(4u);
v___x_1723_ = l_Lean_Expr_isAppOfArity(v_proof_1702_, v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = l_Lean_Expr_getAppFn(v_proof_1702_);
lean_dec_ref(v_proof_1702_);
v___x_1725_ = l_Lean_Expr_isConst(v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___x_1724_);
v___x_1726_ = lean_box(v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v_env_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1728_ = lean_st_ref_get(v_a_1703_);
v_env_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref_n(v_env_1729_, 2);
lean_dec(v___x_1728_);
v___x_1730_ = l_Lean_Expr_constName_x21(v___x_1724_);
lean_dec_ref(v___x_1724_);
v___x_1731_ = l_Lean_defeqAttr;
lean_inc(v___x_1730_);
v___x_1732_ = l_Lean_TagAttribute_hasTag(v___x_1731_, v_env_1729_, v___x_1730_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_backwardDefeqAttr;
v___x_1734_ = l_Lean_TagAttribute_hasTag(v___x_1733_, v_env_1729_, v___x_1730_);
v___x_1735_ = lean_box(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v___x_1730_);
lean_dec_ref(v_env_1729_);
v___x_1737_ = lean_box(v___x_1713_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Expr_appArg_x21(v_proof_1702_);
lean_dec_ref(v_proof_1702_);
v_proof_1702_ = v___x_1739_;
goto _start;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec_ref(v_proof_1702_);
v___x_1741_ = lean_box(v___x_1713_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec_ref(v_proof_1702_);
v___x_1743_ = lean_box(v___x_1713_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* v_type_1745_, lean_object* v_proof_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1745_, v_proof_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_type_1745_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* v_type_1750_, lean_object* v_proof_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1750_, v_proof_1751_, v_a_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* v_type_1756_, lean_object* v_proof_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1756_, v_proof_1757_, v_a_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec_ref(v_type_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object* v_attrName_1762_, lean_object* v_declName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1769_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1770_ = l_Lean_MessageData_ofName(v_attrName_1762_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_MessageData_ofConstName(v_declName_1763_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1778_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1780_, lean_object* v_declName_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1780_, v_declName_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object* v_attrName_1788_, lean_object* v_declName_1789_, lean_object* v_asyncPrefix_x3f_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___y_1797_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1790_) == 0)
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_MessageData_nil;
v___y_1797_ = v___x_1810_;
goto v___jp_1796_;
}
else
{
lean_object* v_val_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_val_1811_ = lean_ctor_get(v_asyncPrefix_x3f_1790_, 0);
lean_inc(v_val_1811_);
lean_dec_ref_known(v_asyncPrefix_x3f_1790_, 1);
v___x_1812_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1813_ = l_Lean_MessageData_ofName(v_val_1811_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___y_1797_ = v___x_1816_;
goto v___jp_1796_;
}
v___jp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1798_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1799_ = l_Lean_MessageData_ofName(v_attrName_1788_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = 0;
v___x_1804_ = l_Lean_MessageData_ofConstName(v_declName_1789_, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1802_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___y_1797_);
v___x_1809_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1808_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1817_, lean_object* v_declName_1818_, lean_object* v_asyncPrefix_x3f_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1817_, v_declName_1818_, v_asyncPrefix_x3f_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object* v_attr_1826_, lean_object* v_decl_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___x_1877_; lean_object* v_env_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___x_1893_; 
v___x_1877_ = lean_st_ref_get(v___y_1831_);
v_env_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc_ref(v_env_1878_);
lean_dec(v___x_1877_);
v___x_1893_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1878_, v_decl_1827_);
if (lean_obj_tag(v___x_1893_) == 0)
{
v___y_1880_ = v___y_1828_;
v___y_1881_ = v___y_1829_;
v___y_1882_ = v___y_1830_;
v___y_1883_ = v___y_1831_;
goto v___jp_1879_;
}
else
{
lean_object* v_attr_1894_; lean_object* v_toAttributeImplCore_1895_; lean_object* v_name_1896_; lean_object* v___x_1897_; 
lean_dec_ref_known(v___x_1893_, 1);
lean_dec_ref(v_env_1878_);
v_attr_1894_ = lean_ctor_get(v_attr_1826_, 0);
lean_inc_ref(v_attr_1894_);
lean_dec_ref(v_attr_1826_);
v_toAttributeImplCore_1895_ = lean_ctor_get(v_attr_1894_, 0);
lean_inc_ref(v_toAttributeImplCore_1895_);
lean_dec_ref(v_attr_1894_);
v_name_1896_ = lean_ctor_get(v_toAttributeImplCore_1895_, 1);
lean_inc(v_name_1896_);
lean_dec_ref(v_toAttributeImplCore_1895_);
v___x_1897_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_1896_, v_decl_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1897_;
}
v___jp_1833_:
{
lean_object* v___x_1836_; lean_object* v_ext_1837_; lean_object* v_toEnvExtension_1838_; lean_object* v_env_1839_; lean_object* v_nextMacroScope_1840_; lean_object* v_ngen_1841_; lean_object* v_auxDeclNGen_1842_; lean_object* v_traceState_1843_; lean_object* v_recordedDeps_1844_; lean_object* v_messages_1845_; lean_object* v_infoState_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1875_; 
v___x_1836_ = lean_st_ref_take(v___y_1835_);
v_ext_1837_ = lean_ctor_get(v_attr_1826_, 1);
lean_inc_ref(v_ext_1837_);
lean_dec_ref(v_attr_1826_);
v_toEnvExtension_1838_ = lean_ctor_get(v_ext_1837_, 0);
v_env_1839_ = lean_ctor_get(v___x_1836_, 0);
v_nextMacroScope_1840_ = lean_ctor_get(v___x_1836_, 1);
v_ngen_1841_ = lean_ctor_get(v___x_1836_, 2);
v_auxDeclNGen_1842_ = lean_ctor_get(v___x_1836_, 3);
v_traceState_1843_ = lean_ctor_get(v___x_1836_, 4);
v_recordedDeps_1844_ = lean_ctor_get(v___x_1836_, 6);
v_messages_1845_ = lean_ctor_get(v___x_1836_, 7);
v_infoState_1846_ = lean_ctor_get(v___x_1836_, 8);
v_snapshotTasks_1847_ = lean_ctor_get(v___x_1836_, 9);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v___x_1836_, 5);
lean_dec(v_unused_1876_);
v___x_1849_ = v___x_1836_;
v_isShared_1850_ = v_isSharedCheck_1875_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snapshotTasks_1847_);
lean_inc(v_infoState_1846_);
lean_inc(v_messages_1845_);
lean_inc(v_recordedDeps_1844_);
lean_inc(v_traceState_1843_);
lean_inc(v_auxDeclNGen_1842_);
lean_inc(v_ngen_1841_);
lean_inc(v_nextMacroScope_1840_);
lean_inc(v_env_1839_);
lean_dec(v___x_1836_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1875_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_asyncMode_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v_asyncMode_1851_ = lean_ctor_get(v_toEnvExtension_1838_, 2);
lean_inc(v_asyncMode_1851_);
lean_inc(v_decl_1827_);
v___x_1852_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1837_, v_env_1839_, v_decl_1827_, v_asyncMode_1851_, v_decl_1827_);
lean_dec(v_asyncMode_1851_);
v___x_1853_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 5, v___x_1853_);
lean_ctor_set(v___x_1849_, 0, v___x_1852_);
v___x_1855_ = v___x_1849_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1840_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1841_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1842_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_traceState_1843_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_recordedDeps_1844_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v_messages_1845_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_infoState_1846_);
lean_ctor_set(v_reuseFailAlloc_1874_, 9, v_snapshotTasks_1847_);
v___x_1855_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_mctx_1858_; lean_object* v_zetaDeltaFVarIds_1859_; lean_object* v_postponed_1860_; lean_object* v_diag_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1872_; 
v___x_1856_ = lean_st_ref_put(v___y_1835_, v___x_1855_);
v___x_1857_ = lean_st_ref_take(v___y_1834_);
v_mctx_1858_ = lean_ctor_get(v___x_1857_, 0);
v_zetaDeltaFVarIds_1859_ = lean_ctor_get(v___x_1857_, 2);
v_postponed_1860_ = lean_ctor_get(v___x_1857_, 3);
v_diag_1861_ = lean_ctor_get(v___x_1857_, 4);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___x_1857_, 1);
lean_dec(v_unused_1873_);
v___x_1863_ = v___x_1857_;
v_isShared_1864_ = v_isSharedCheck_1872_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_diag_1861_);
lean_inc(v_postponed_1860_);
lean_inc(v_zetaDeltaFVarIds_1859_);
lean_inc(v_mctx_1858_);
lean_dec(v___x_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1872_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1866_);
v___x_1868_ = v___x_1863_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_mctx_1858_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_zetaDeltaFVarIds_1859_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_postponed_1860_);
lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_diag_1861_);
v___x_1868_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_st_ref_put(v___y_1834_, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1865_);
return v___x_1870_;
}
}
}
}
}
v___jp_1879_:
{
lean_object* v_ext_1884_; lean_object* v_toEnvExtension_1885_; lean_object* v_attr_1886_; lean_object* v_asyncMode_1887_; uint8_t v___x_1888_; 
v_ext_1884_ = lean_ctor_get(v_attr_1826_, 1);
v_toEnvExtension_1885_ = lean_ctor_get(v_ext_1884_, 0);
v_attr_1886_ = lean_ctor_get(v_attr_1826_, 0);
v_asyncMode_1887_ = lean_ctor_get(v_toEnvExtension_1885_, 2);
lean_inc(v_decl_1827_);
lean_inc_ref(v_env_1878_);
v___x_1888_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1878_, v_decl_1827_, v_asyncMode_1887_);
if (v___x_1888_ == 0)
{
lean_object* v_toAttributeImplCore_1889_; lean_object* v_name_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_inc_ref(v_attr_1886_);
lean_dec_ref(v_attr_1826_);
v_toAttributeImplCore_1889_ = lean_ctor_get(v_attr_1886_, 0);
lean_inc_ref(v_toAttributeImplCore_1889_);
lean_dec_ref(v_attr_1886_);
v_name_1890_ = lean_ctor_get(v_toAttributeImplCore_1889_, 1);
lean_inc(v_name_1890_);
lean_dec_ref(v_toAttributeImplCore_1889_);
v___x_1891_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1878_);
v___x_1892_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_1890_, v_decl_1827_, v___x_1891_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1892_;
}
else
{
lean_dec_ref(v_env_1878_);
v___y_1834_ = v___y_1881_;
v___y_1835_ = v___y_1883_;
goto v___jp_1833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object* v_attr_1898_, lean_object* v_decl_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_1898_, v_decl_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(lean_object* v_msg_1906_, lean_object* v_declHint_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_env_1912_; uint8_t v___x_1913_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_st_ref_get(v___y_1908_);
v_env_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_env_1912_);
lean_dec(v___x_1911_);
v___x_1913_ = l_Lean_Name_isAnonymous(v_declHint_1907_);
if (v___x_1913_ == 0)
{
uint8_t v_isExporting_1914_; 
v_isExporting_1914_ = lean_ctor_get_uint8(v_env_1912_, sizeof(void*)*8);
if (v_isExporting_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v_env_1912_);
lean_dec(v_declHint_1907_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_msg_1906_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
lean_inc_ref(v_env_1912_);
v___x_1916_ = l_Lean_Environment_setExporting(v_env_1912_, v___x_1913_);
lean_inc(v_declHint_1907_);
lean_inc_ref(v___x_1916_);
v___x_1917_ = l_Lean_Environment_contains(v___x_1916_, v_declHint_1907_, v_isExporting_1914_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v___x_1916_);
lean_dec_ref(v_env_1912_);
lean_dec(v_declHint_1907_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1906_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_c_1926_; lean_object* v___x_1927_; 
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1920_ = lean_unsigned_to_nat(32u);
v___x_1921_ = lean_mk_empty_array_with_capacity(v___x_1920_);
lean_dec_ref(v___x_1921_);
v___x_1922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1923_ = l_Lean_Options_empty;
v___x_1924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1916_);
lean_ctor_set(v___x_1924_, 1, v___x_1919_);
lean_ctor_set(v___x_1924_, 2, v___x_1922_);
lean_ctor_set(v___x_1924_, 3, v___x_1923_);
lean_inc(v_declHint_1907_);
v___x_1925_ = l_Lean_MessageData_ofConstName(v_declHint_1907_, v___x_1913_);
v_c_1926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1926_, 0, v___x_1924_);
lean_ctor_set(v_c_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1912_, v_declHint_1907_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec_ref(v_env_1912_);
lean_dec(v_declHint_1907_);
v___x_1928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_c_1926_);
v___x_1930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_MessageData_note(v___x_1931_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_msg_1906_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1969_; 
v_val_1935_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1937_ = v___x_1927_;
v_isShared_1938_ = v_isSharedCheck_1969_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_val_1935_);
lean_dec(v___x_1927_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1969_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v_mod_1941_; uint8_t v___x_1942_; 
v___x_1939_ = l_Lean_Environment_header(v_env_1912_);
lean_dec_ref(v_env_1912_);
v___x_1940_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1939_);
v_mod_1941_ = lean_array_get(v___x_1910_, v___x_1940_, v_val_1935_);
lean_dec(v_val_1935_);
lean_dec_ref(v___x_1940_);
v___x_1942_ = l_Lean_isPrivateName(v_declHint_1907_);
lean_dec(v_declHint_1907_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_c_1926_);
v___x_1945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_MessageData_ofName(v_mod_1941_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = l_Lean_MessageData_note(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_msg_1906_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1952_);
v___x_1954_ = v___x_1937_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_c_1926_);
v___x_1958_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = l_Lean_MessageData_ofName(v_mod_1941_);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_MessageData_note(v___x_1963_);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_msg_1906_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1965_);
v___x_1967_ = v___x_1937_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1970_; 
lean_dec_ref(v_env_1912_);
lean_dec(v_declHint_1907_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_msg_1906_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_msg_1971_, lean_object* v_declHint_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_1971_, v_declHint_1972_, v___y_1973_);
lean_dec(v___y_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object* v_msg_1976_, lean_object* v_declHint_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1993_; 
v___x_1983_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_1976_, v_declHint_1977_, v___y_1981_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1993_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1988_ = l_Lean_unknownIdentifierMessageTag;
v___x_1989_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_a_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1989_);
v___x_1991_ = v___x_1986_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object* v_msg_1994_, lean_object* v_declHint_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1994_, v_declHint_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object* v_ref_2002_, lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_toCold_2009_; lean_object* v_currRecDepth_2010_; lean_object* v_ref_2011_; uint16_t v_optionFlags_2012_; uint8_t v_suppressElabErrors_2013_; uint8_t v_isRecordingDeps_2014_; lean_object* v_ref_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_toCold_2009_ = lean_ctor_get(v___y_2006_, 0);
v_currRecDepth_2010_ = lean_ctor_get(v___y_2006_, 1);
v_ref_2011_ = lean_ctor_get(v___y_2006_, 2);
v_optionFlags_2012_ = lean_ctor_get_uint16(v___y_2006_, sizeof(void*)*3);
v_suppressElabErrors_2013_ = lean_ctor_get_uint8(v___y_2006_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2014_ = lean_ctor_get_uint8(v___y_2006_, sizeof(void*)*3 + 3);
v_ref_2015_ = l_Lean_replaceRef(v_ref_2002_, v_ref_2011_);
lean_inc(v_currRecDepth_2010_);
lean_inc_ref(v_toCold_2009_);
v___x_2016_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2016_, 0, v_toCold_2009_);
lean_ctor_set(v___x_2016_, 1, v_currRecDepth_2010_);
lean_ctor_set(v___x_2016_, 2, v_ref_2015_);
lean_ctor_set_uint16(v___x_2016_, sizeof(void*)*3, v_optionFlags_2012_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 2, v_suppressElabErrors_2013_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 3, v_isRecordingDeps_2014_);
v___x_2017_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_2003_, v___y_2004_, v___y_2005_, v___x_2016_, v___y_2007_);
lean_dec_ref_known(v___x_2016_, 3);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_ref_2018_, lean_object* v_msg_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2018_, v_msg_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_ref_2018_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object* v_ref_2026_, lean_object* v_msg_2027_, lean_object* v_declHint_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v_a_2035_; lean_object* v___x_2036_; 
v___x_2034_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_2027_, v_declHint_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2026_, v_a_2035_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_ref_2037_, lean_object* v_msg_2038_, lean_object* v_declHint_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2037_, v_msg_2038_, v_declHint_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v_ref_2037_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object* v_ref_2046_, lean_object* v_constName_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2053_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_2054_ = 0;
lean_inc(v_constName_2047_);
v___x_2055_ = l_Lean_MessageData_ofConstName(v_constName_2047_, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2046_, v___x_2058_, v_constName_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object* v_ref_2060_, lean_object* v_constName_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2060_, v_constName_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v_ref_2060_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object* v_constName_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_ref_2074_; lean_object* v___x_2075_; 
v_ref_2074_ = lean_ctor_get(v___y_2071_, 2);
v___x_2075_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2074_, v_constName_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object* v_constName_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object* v_constName_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v_env_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_st_ref_get(v___y_2087_);
v_env_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc_ref(v_env_2090_);
lean_dec(v___x_2089_);
v___x_2091_ = 0;
lean_inc(v_constName_2083_);
v___x_2092_ = l_Lean_Environment_find_x3f(v_env_2090_, v_constName_2083_, v___x_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2093_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_constName_2083_);
v_val_2094_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2092_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v___x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 0);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_val_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object* v_constName_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(lean_object* v_opts_2109_, lean_object* v_opt_2110_){
_start:
{
lean_object* v_name_2111_; lean_object* v_defValue_2112_; lean_object* v_map_2113_; lean_object* v___x_2114_; 
v_name_2111_ = lean_ctor_get(v_opt_2110_, 0);
v_defValue_2112_ = lean_ctor_get(v_opt_2110_, 1);
v_map_2113_ = lean_ctor_get(v_opts_2109_, 0);
v___x_2114_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2113_, v_name_2111_);
if (lean_obj_tag(v___x_2114_) == 0)
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_unbox(v_defValue_2112_);
return v___x_2115_;
}
else
{
lean_object* v_val_2116_; 
v_val_2116_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v___x_2114_, 1);
if (lean_obj_tag(v_val_2116_) == 1)
{
uint8_t v_v_2117_; 
v_v_2117_ = lean_ctor_get_uint8(v_val_2116_, 0);
lean_dec_ref_known(v_val_2116_, 0);
return v_v_2117_;
}
else
{
uint8_t v___x_2118_; 
lean_dec(v_val_2116_);
v___x_2118_ = lean_unbox(v_defValue_2112_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_2119_, lean_object* v_opt_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(v_opts_2119_, v_opt_2120_);
lean_dec_ref(v_opt_2120_);
lean_dec_ref(v_opts_2119_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_2130_, uint8_t v___y_2131_, lean_object* v_x_2132_){
_start:
{
if (lean_obj_tag(v_x_2132_) == 1)
{
lean_object* v_pre_2133_; 
v_pre_2133_ = lean_ctor_get(v_x_2132_, 0);
switch(lean_obj_tag(v_pre_2133_))
{
case 1:
{
lean_object* v_pre_2134_; 
v_pre_2134_ = lean_ctor_get(v_pre_2133_, 0);
switch(lean_obj_tag(v_pre_2134_))
{
case 0:
{
lean_object* v_str_2135_; lean_object* v_str_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_str_2135_ = lean_ctor_get(v_x_2132_, 1);
v_str_2136_ = lean_ctor_get(v_pre_2133_, 1);
v___x_2137_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0));
v___x_2138_ = lean_string_dec_eq(v_str_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1));
v___x_2140_ = lean_string_dec_eq(v_str_2136_, v___x_2139_);
if (v___x_2140_ == 0)
{
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2));
v___x_2142_ = lean_string_dec_eq(v_str_2135_, v___x_2141_);
if (v___x_2142_ == 0)
{
return v___x_2142_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
else
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3));
v___x_2144_ = lean_string_dec_eq(v_str_2135_, v___x_2143_);
if (v___x_2144_ == 0)
{
return v___x_2144_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
case 1:
{
lean_object* v_pre_2145_; 
v_pre_2145_ = lean_ctor_get(v_pre_2134_, 0);
if (lean_obj_tag(v_pre_2145_) == 0)
{
lean_object* v_str_2146_; lean_object* v_str_2147_; lean_object* v_str_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_str_2146_ = lean_ctor_get(v_x_2132_, 1);
v_str_2147_ = lean_ctor_get(v_pre_2133_, 1);
v_str_2148_ = lean_ctor_get(v_pre_2134_, 1);
v___x_2149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4));
v___x_2150_ = lean_string_dec_eq(v_str_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5));
v___x_2152_ = lean_string_dec_eq(v_str_2147_, v___x_2151_);
if (v___x_2152_ == 0)
{
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6));
v___x_2154_ = lean_string_dec_eq(v_str_2146_, v___x_2153_);
if (v___x_2154_ == 0)
{
return v___x_2154_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
}
else
{
return v___y_2131_;
}
}
default: 
{
return v___y_2131_;
}
}
}
case 0:
{
lean_object* v_str_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_str_2155_ = lean_ctor_get(v_x_2132_, 1);
v___x_2156_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0));
v___x_2157_ = lean_string_dec_eq(v_str_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
return v___x_2157_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
default: 
{
return v___y_2131_;
}
}
}
else
{
return v___y_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_2158_, lean_object* v___y_2159_, lean_object* v_x_2160_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2161_; uint8_t v___y_8468__boxed_2162_; uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_suppressElabErrors_boxed_2161_ = lean_unbox(v_suppressElabErrors_2158_);
v___y_8468__boxed_2162_ = lean_unbox(v___y_2159_);
v_res_2163_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_2161_, v___y_8468__boxed_2162_, v_x_2160_);
lean_dec(v_x_2160_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object* v_ref_2166_, lean_object* v_msgData_2167_, uint8_t v_severity_2168_, uint8_t v_isSilent_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___y_2176_; lean_object* v___y_2177_; uint8_t v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v_toCold_2183_; lean_object* v___y_2184_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; uint8_t v___y_2217_; uint8_t v___y_2218_; uint8_t v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2240_; lean_object* v___y_2241_; uint8_t v___y_2242_; uint8_t v___y_2243_; uint8_t v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2250_; uint8_t v___y_2251_; uint8_t v___y_2252_; uint8_t v___x_2263_; uint8_t v___y_2265_; uint8_t v___y_2266_; uint8_t v___y_2267_; uint8_t v___y_2269_; uint8_t v___x_2277_; 
v___x_2263_ = 2;
v___x_2277_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2168_, v___x_2263_);
if (v___x_2277_ == 0)
{
v___y_2269_ = v___x_2277_;
goto v___jp_2268_;
}
else
{
uint8_t v___x_2278_; 
lean_inc_ref(v_msgData_2167_);
v___x_2278_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2167_);
v___y_2269_ = v___x_2278_;
goto v___jp_2268_;
}
v___jp_2175_:
{
lean_object* v_currNamespace_2185_; lean_object* v_openDecls_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_env_2191_; lean_object* v_nextMacroScope_2192_; lean_object* v_ngen_2193_; lean_object* v_auxDeclNGen_2194_; lean_object* v_traceState_2195_; lean_object* v_cache_2196_; lean_object* v_recordedDeps_2197_; lean_object* v_messages_2198_; lean_object* v_infoState_2199_; lean_object* v_snapshotTasks_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2211_; 
v_currNamespace_2185_ = lean_ctor_get(v_toCold_2183_, 4);
v_openDecls_2186_ = lean_ctor_get(v_toCold_2183_, 5);
lean_inc(v_openDecls_2186_);
lean_inc(v_currNamespace_2185_);
v___x_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_currNamespace_2185_);
lean_ctor_set(v___x_2187_, 1, v_openDecls_2186_);
v___x_2188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___y_2181_);
lean_inc_ref(v___y_2179_);
lean_inc_ref(v___y_2180_);
v___x_2189_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2189_, 0, v___y_2180_);
lean_ctor_set(v___x_2189_, 1, v___y_2182_);
lean_ctor_set(v___x_2189_, 2, v___y_2177_);
lean_ctor_set(v___x_2189_, 3, v___y_2179_);
lean_ctor_set(v___x_2189_, 4, v___x_2188_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*5, v___y_2176_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*5 + 1, v___y_2178_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*5 + 2, v_isSilent_2169_);
v___x_2190_ = lean_st_ref_take(v___y_2184_);
v_env_2191_ = lean_ctor_get(v___x_2190_, 0);
v_nextMacroScope_2192_ = lean_ctor_get(v___x_2190_, 1);
v_ngen_2193_ = lean_ctor_get(v___x_2190_, 2);
v_auxDeclNGen_2194_ = lean_ctor_get(v___x_2190_, 3);
v_traceState_2195_ = lean_ctor_get(v___x_2190_, 4);
v_cache_2196_ = lean_ctor_get(v___x_2190_, 5);
v_recordedDeps_2197_ = lean_ctor_get(v___x_2190_, 6);
v_messages_2198_ = lean_ctor_get(v___x_2190_, 7);
v_infoState_2199_ = lean_ctor_get(v___x_2190_, 8);
v_snapshotTasks_2200_ = lean_ctor_get(v___x_2190_, 9);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2202_ = v___x_2190_;
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_snapshotTasks_2200_);
lean_inc(v_infoState_2199_);
lean_inc(v_messages_2198_);
lean_inc(v_recordedDeps_2197_);
lean_inc(v_cache_2196_);
lean_inc(v_traceState_2195_);
lean_inc(v_auxDeclNGen_2194_);
lean_inc(v_ngen_2193_);
lean_inc(v_nextMacroScope_2192_);
lean_inc(v_env_2191_);
lean_dec(v___x_2190_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = l_Lean_MessageLog_add(v___x_2189_, v_messages_2198_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 7, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_env_2191_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_nextMacroScope_2192_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_ngen_2193_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_auxDeclNGen_2194_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_traceState_2195_);
lean_ctor_set(v_reuseFailAlloc_2210_, 5, v_cache_2196_);
lean_ctor_set(v_reuseFailAlloc_2210_, 6, v_recordedDeps_2197_);
lean_ctor_set(v_reuseFailAlloc_2210_, 7, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2210_, 8, v_infoState_2199_);
lean_ctor_set(v_reuseFailAlloc_2210_, 9, v_snapshotTasks_2200_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_st_ref_put(v___y_2184_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2204_);
return v___x_2209_;
}
}
}
v___jp_2212_:
{
lean_object* v_fileName_2221_; lean_object* v_fileMap_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2238_; 
v_fileName_2221_ = lean_ctor_get(v___y_2216_, 0);
v_fileMap_2222_ = lean_ctor_get(v___y_2216_, 1);
v___x_2223_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2167_);
v___x_2224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_2223_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_inc_ref_n(v_fileMap_2222_, 2);
v___x_2229_ = l_Lean_FileMap_toPosition(v_fileMap_2222_, v___y_2215_);
lean_dec(v___y_2215_);
v___x_2230_ = l_Lean_FileMap_toPosition(v_fileMap_2222_, v___y_2220_);
lean_dec(v___y_2220_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
v___x_2232_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0));
if (v___y_2219_ == 0)
{
lean_del_object(v___x_2227_);
lean_dec_ref(v___y_2214_);
v___y_2176_ = v___y_2217_;
v___y_2177_ = v___x_2231_;
v___y_2178_ = v___y_2218_;
v___y_2179_ = v___x_2232_;
v___y_2180_ = v_fileName_2221_;
v___y_2181_ = v_a_2225_;
v___y_2182_ = v___x_2229_;
v_toCold_2183_ = v___y_2213_;
v___y_2184_ = v___y_2173_;
goto v___jp_2175_;
}
else
{
uint8_t v___x_2233_; 
lean_inc(v_a_2225_);
v___x_2233_ = l_Lean_MessageData_hasTag(v___y_2214_, v_a_2225_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2231_, 1);
lean_dec_ref(v___x_2229_);
lean_dec(v_a_2225_);
v___x_2234_ = lean_box(0);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2234_);
v___x_2236_ = v___x_2227_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_del_object(v___x_2227_);
v___y_2176_ = v___y_2217_;
v___y_2177_ = v___x_2231_;
v___y_2178_ = v___y_2218_;
v___y_2179_ = v___x_2232_;
v___y_2180_ = v_fileName_2221_;
v___y_2181_ = v_a_2225_;
v___y_2182_ = v___x_2229_;
v_toCold_2183_ = v___y_2213_;
v___y_2184_ = v___y_2173_;
goto v___jp_2175_;
}
}
}
}
v___jp_2239_:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Syntax_getTailPos_x3f(v___y_2245_, v___y_2243_);
lean_dec(v___y_2245_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_inc(v___y_2246_);
v___y_2213_ = v___y_2240_;
v___y_2214_ = v___y_2241_;
v___y_2215_ = v___y_2246_;
v___y_2216_ = v___y_2240_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2244_;
v___y_2219_ = v___y_2242_;
v___y_2220_ = v___y_2246_;
goto v___jp_2212_;
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v___y_2213_ = v___y_2240_;
v___y_2214_ = v___y_2241_;
v___y_2215_ = v___y_2246_;
v___y_2216_ = v___y_2240_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2244_;
v___y_2219_ = v___y_2242_;
v___y_2220_ = v_val_2248_;
goto v___jp_2212_;
}
}
v___jp_2249_:
{
lean_object* v_toCold_2253_; lean_object* v_ref_2254_; uint8_t v_suppressElabErrors_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v_ref_2259_; lean_object* v___x_2260_; 
v_toCold_2253_ = lean_ctor_get(v___y_2172_, 0);
v_ref_2254_ = lean_ctor_get(v___y_2172_, 2);
v_suppressElabErrors_2255_ = lean_ctor_get_uint8(v___y_2172_, sizeof(void*)*3 + 2);
v___x_2256_ = lean_box(v_suppressElabErrors_2255_);
v___x_2257_ = lean_box(v___y_2250_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2258_, 0, v___x_2256_);
lean_closure_set(v___f_2258_, 1, v___x_2257_);
v_ref_2259_ = l_Lean_replaceRef(v_ref_2166_, v_ref_2254_);
v___x_2260_ = l_Lean_Syntax_getPos_x3f(v_ref_2259_, v___y_2251_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_unsigned_to_nat(0u);
v___y_2240_ = v_toCold_2253_;
v___y_2241_ = v___f_2258_;
v___y_2242_ = v_suppressElabErrors_2255_;
v___y_2243_ = v___y_2251_;
v___y_2244_ = v___y_2252_;
v___y_2245_ = v_ref_2259_;
v___y_2246_ = v___x_2261_;
goto v___jp_2239_;
}
else
{
lean_object* v_val_2262_; 
v_val_2262_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_val_2262_);
lean_dec_ref_known(v___x_2260_, 1);
v___y_2240_ = v_toCold_2253_;
v___y_2241_ = v___f_2258_;
v___y_2242_ = v_suppressElabErrors_2255_;
v___y_2243_ = v___y_2251_;
v___y_2244_ = v___y_2252_;
v___y_2245_ = v_ref_2259_;
v___y_2246_ = v_val_2262_;
goto v___jp_2239_;
}
}
v___jp_2264_:
{
if (v___y_2267_ == 0)
{
v___y_2250_ = v___y_2265_;
v___y_2251_ = v___y_2266_;
v___y_2252_ = v_severity_2168_;
goto v___jp_2249_;
}
else
{
v___y_2250_ = v___y_2265_;
v___y_2251_ = v___y_2266_;
v___y_2252_ = v___x_2263_;
goto v___jp_2249_;
}
}
v___jp_2268_:
{
if (v___y_2269_ == 0)
{
uint8_t v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = 1;
v___x_2271_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2168_, v___x_2270_);
if (v___x_2271_ == 0)
{
v___y_2265_ = v___y_2269_;
v___y_2266_ = v___y_2269_;
v___y_2267_ = v___x_2271_;
goto v___jp_2264_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2272_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2172_);
v___x_2273_ = l_Lean_warningAsError;
v___x_2274_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(v___x_2272_, v___x_2273_);
lean_dec_ref(v___x_2272_);
v___y_2265_ = v___y_2269_;
v___y_2266_ = v___y_2269_;
v___y_2267_ = v___x_2274_;
goto v___jp_2264_;
}
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v_msgData_2167_);
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object* v_ref_2279_, lean_object* v_msgData_2280_, lean_object* v_severity_2281_, lean_object* v_isSilent_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_severity_boxed_2288_; uint8_t v_isSilent_boxed_2289_; lean_object* v_res_2290_; 
v_severity_boxed_2288_ = lean_unbox(v_severity_2281_);
v_isSilent_boxed_2289_ = lean_unbox(v_isSilent_2282_);
v_res_2290_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2279_, v_msgData_2280_, v_severity_boxed_2288_, v_isSilent_boxed_2289_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_ref_2279_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object* v_msgData_2291_, uint8_t v_severity_2292_, uint8_t v_isSilent_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_ref_2299_; lean_object* v___x_2300_; 
v_ref_2299_ = lean_ctor_get(v___y_2296_, 2);
v___x_2300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2299_, v_msgData_2291_, v_severity_2292_, v_isSilent_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object* v_msgData_2301_, lean_object* v_severity_2302_, lean_object* v_isSilent_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v_severity_boxed_2309_; uint8_t v_isSilent_boxed_2310_; lean_object* v_res_2311_; 
v_severity_boxed_2309_ = lean_unbox(v_severity_2302_);
v_isSilent_boxed_2310_ = lean_unbox(v_isSilent_2303_);
v_res_2311_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2301_, v_severity_boxed_2309_, v_isSilent_boxed_2310_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object* v_msgData_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = 2;
v___x_2319_ = 0;
v___x_2320_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2312_, v___x_2318_, v___x_2319_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object* v_msgData_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object* v___y_2328_, uint8_t v_isExporting_2329_, lean_object* v___x_2330_, lean_object* v___y_2331_, lean_object* v___x_2332_, lean_object* v_a_x3f_2333_){
_start:
{
lean_object* v___x_2335_; lean_object* v_env_2336_; lean_object* v_nextMacroScope_2337_; lean_object* v_ngen_2338_; lean_object* v_auxDeclNGen_2339_; lean_object* v_traceState_2340_; lean_object* v_recordedDeps_2341_; lean_object* v_messages_2342_; lean_object* v_infoState_2343_; lean_object* v_snapshotTasks_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2369_; 
v___x_2335_ = lean_st_ref_take(v___y_2328_);
v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
v_nextMacroScope_2337_ = lean_ctor_get(v___x_2335_, 1);
v_ngen_2338_ = lean_ctor_get(v___x_2335_, 2);
v_auxDeclNGen_2339_ = lean_ctor_get(v___x_2335_, 3);
v_traceState_2340_ = lean_ctor_get(v___x_2335_, 4);
v_recordedDeps_2341_ = lean_ctor_get(v___x_2335_, 6);
v_messages_2342_ = lean_ctor_get(v___x_2335_, 7);
v_infoState_2343_ = lean_ctor_get(v___x_2335_, 8);
v_snapshotTasks_2344_ = lean_ctor_get(v___x_2335_, 9);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2335_, 5);
lean_dec(v_unused_2370_);
v___x_2346_ = v___x_2335_;
v_isShared_2347_ = v_isSharedCheck_2369_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_snapshotTasks_2344_);
lean_inc(v_infoState_2343_);
lean_inc(v_messages_2342_);
lean_inc(v_recordedDeps_2341_);
lean_inc(v_traceState_2340_);
lean_inc(v_auxDeclNGen_2339_);
lean_inc(v_ngen_2338_);
lean_inc(v_nextMacroScope_2337_);
lean_inc(v_env_2336_);
lean_dec(v___x_2335_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2369_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = l_Lean_Environment_setExporting(v_env_2336_, v_isExporting_2329_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 5, v___x_2330_);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_nextMacroScope_2337_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_ngen_2338_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_auxDeclNGen_2339_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v_traceState_2340_);
lean_ctor_set(v_reuseFailAlloc_2368_, 5, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2368_, 6, v_recordedDeps_2341_);
lean_ctor_set(v_reuseFailAlloc_2368_, 7, v_messages_2342_);
lean_ctor_set(v_reuseFailAlloc_2368_, 8, v_infoState_2343_);
lean_ctor_set(v_reuseFailAlloc_2368_, 9, v_snapshotTasks_2344_);
v___x_2350_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_mctx_2353_; lean_object* v_zetaDeltaFVarIds_2354_; lean_object* v_postponed_2355_; lean_object* v_diag_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2366_; 
v___x_2351_ = lean_st_ref_put(v___y_2328_, v___x_2350_);
v___x_2352_ = lean_st_ref_take(v___y_2331_);
v_mctx_2353_ = lean_ctor_get(v___x_2352_, 0);
v_zetaDeltaFVarIds_2354_ = lean_ctor_get(v___x_2352_, 2);
v_postponed_2355_ = lean_ctor_get(v___x_2352_, 3);
v_diag_2356_ = lean_ctor_get(v___x_2352_, 4);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v___x_2352_, 1);
lean_dec(v_unused_2367_);
v___x_2358_ = v___x_2352_;
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_diag_2356_);
lean_inc(v_postponed_2355_);
lean_inc(v_zetaDeltaFVarIds_2354_);
lean_inc(v_mctx_2353_);
lean_dec(v___x_2352_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_box(0);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v___x_2332_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_mctx_2353_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_zetaDeltaFVarIds_2354_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_postponed_2355_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_diag_2356_);
v___x_2362_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_st_ref_put(v___y_2331_, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2360_);
return v___x_2364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object* v___y_2371_, lean_object* v_isExporting_2372_, lean_object* v___x_2373_, lean_object* v___y_2374_, lean_object* v___x_2375_, lean_object* v_a_x3f_2376_, lean_object* v___y_2377_){
_start:
{
uint8_t v_isExporting_boxed_2378_; lean_object* v_res_2379_; 
v_isExporting_boxed_2378_ = lean_unbox(v_isExporting_2372_);
v_res_2379_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2371_, v_isExporting_boxed_2378_, v___x_2373_, v___y_2374_, v___x_2375_, v_a_x3f_2376_);
lean_dec(v_a_x3f_2376_);
lean_dec(v___y_2374_);
lean_dec(v___y_2371_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object* v_declName_2380_, uint8_t v_isExporting_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v_env_2387_; lean_object* v___x_2388_; uint8_t v_isModule_2389_; 
v___x_2386_ = lean_st_ref_get(v___y_2384_);
v_env_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_env_2387_);
lean_dec(v___x_2386_);
v___x_2388_ = l_Lean_Environment_header(v_env_2387_);
v_isModule_2389_ = lean_ctor_get_uint8(v___x_2388_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2388_);
if (v_isModule_2389_ == 0)
{
lean_object* v___x_2390_; 
lean_dec_ref(v_env_2387_);
v___x_2390_ = l_Lean_validateDefEqAttr(v_declName_2380_, v___y_2383_, v___y_2384_);
return v___x_2390_;
}
else
{
uint8_t v_isExporting_2391_; 
v_isExporting_2391_ = lean_ctor_get_uint8(v_env_2387_, sizeof(void*)*8);
lean_dec_ref(v_env_2387_);
if (v_isExporting_2381_ == 0)
{
if (v_isExporting_2391_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_validateDefEqAttr(v_declName_2380_, v___y_2383_, v___y_2384_);
return v___x_2458_;
}
else
{
goto v___jp_2392_;
}
}
else
{
if (v_isExporting_2391_ == 0)
{
goto v___jp_2392_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_validateDefEqAttr(v_declName_2380_, v___y_2383_, v___y_2384_);
return v___x_2459_;
}
}
v___jp_2392_:
{
lean_object* v___x_2393_; lean_object* v_env_2394_; lean_object* v_nextMacroScope_2395_; lean_object* v_ngen_2396_; lean_object* v_auxDeclNGen_2397_; lean_object* v_traceState_2398_; lean_object* v_recordedDeps_2399_; lean_object* v_messages_2400_; lean_object* v_infoState_2401_; lean_object* v_snapshotTasks_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2456_; 
v___x_2393_ = lean_st_ref_take(v___y_2384_);
v_env_2394_ = lean_ctor_get(v___x_2393_, 0);
v_nextMacroScope_2395_ = lean_ctor_get(v___x_2393_, 1);
v_ngen_2396_ = lean_ctor_get(v___x_2393_, 2);
v_auxDeclNGen_2397_ = lean_ctor_get(v___x_2393_, 3);
v_traceState_2398_ = lean_ctor_get(v___x_2393_, 4);
v_recordedDeps_2399_ = lean_ctor_get(v___x_2393_, 6);
v_messages_2400_ = lean_ctor_get(v___x_2393_, 7);
v_infoState_2401_ = lean_ctor_get(v___x_2393_, 8);
v_snapshotTasks_2402_ = lean_ctor_get(v___x_2393_, 9);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v___x_2393_, 5);
lean_dec(v_unused_2457_);
v___x_2404_ = v___x_2393_;
v_isShared_2405_ = v_isSharedCheck_2456_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snapshotTasks_2402_);
lean_inc(v_infoState_2401_);
lean_inc(v_messages_2400_);
lean_inc(v_recordedDeps_2399_);
lean_inc(v_traceState_2398_);
lean_inc(v_auxDeclNGen_2397_);
lean_inc(v_ngen_2396_);
lean_inc(v_nextMacroScope_2395_);
lean_inc(v_env_2394_);
lean_dec(v___x_2393_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2456_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = l_Lean_Environment_setExporting(v_env_2394_, v_isExporting_2381_);
v___x_2407_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 5, v___x_2407_);
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_nextMacroScope_2395_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_ngen_2396_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_auxDeclNGen_2397_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_traceState_2398_);
lean_ctor_set(v_reuseFailAlloc_2455_, 5, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2455_, 6, v_recordedDeps_2399_);
lean_ctor_set(v_reuseFailAlloc_2455_, 7, v_messages_2400_);
lean_ctor_set(v_reuseFailAlloc_2455_, 8, v_infoState_2401_);
lean_ctor_set(v_reuseFailAlloc_2455_, 9, v_snapshotTasks_2402_);
v___x_2409_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v_mctx_2412_; lean_object* v_zetaDeltaFVarIds_2413_; lean_object* v_postponed_2414_; lean_object* v_diag_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2453_; 
v___x_2410_ = lean_st_ref_put(v___y_2384_, v___x_2409_);
v___x_2411_ = lean_st_ref_take(v___y_2382_);
v_mctx_2412_ = lean_ctor_get(v___x_2411_, 0);
v_zetaDeltaFVarIds_2413_ = lean_ctor_get(v___x_2411_, 2);
v_postponed_2414_ = lean_ctor_get(v___x_2411_, 3);
v_diag_2415_ = lean_ctor_get(v___x_2411_, 4);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2411_, 1);
lean_dec(v_unused_2454_);
v___x_2417_ = v___x_2411_;
v_isShared_2418_ = v_isSharedCheck_2453_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_diag_2415_);
lean_inc(v_postponed_2414_);
lean_inc(v_zetaDeltaFVarIds_2413_);
lean_inc(v_mctx_2412_);
lean_dec(v___x_2411_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2453_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 1, v___x_2419_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_mctx_2412_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_zetaDeltaFVarIds_2413_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_postponed_2414_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_diag_2415_);
v___x_2421_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v_r_2423_; 
v___x_2422_ = lean_st_ref_put(v___y_2382_, v___x_2421_);
v_r_2423_ = l_Lean_validateDefEqAttr(v_declName_2380_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v_r_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2440_; 
v_a_2424_ = lean_ctor_get(v_r_2423_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_r_2423_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2426_ = v_r_2423_;
v_isShared_2427_ = v_isSharedCheck_2440_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v_r_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2440_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
lean_inc(v_a_2424_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 1);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v___x_2430_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2384_, v_isExporting_2391_, v___x_2407_, v___y_2382_, v___x_2419_, v___x_2429_);
lean_dec_ref(v___x_2429_);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; 
v_unused_2438_ = lean_ctor_get(v___x_2430_, 0);
lean_dec(v_unused_2438_);
v___x_2432_ = v___x_2430_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_dec(v___x_2430_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_a_2424_);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2424_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2441_ = lean_ctor_get(v_r_2423_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v_r_2423_, 1);
v___x_2442_ = lean_box(0);
v___x_2443_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2384_, v_isExporting_2391_, v___x_2407_, v___y_2382_, v___x_2419_, v___x_2442_);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2443_, 0);
lean_dec(v_unused_2451_);
v___x_2445_ = v___x_2443_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_dec(v___x_2443_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 1);
lean_ctor_set(v___x_2445_, 0, v_a_2441_);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2441_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object* v_declName_2460_, lean_object* v_isExporting_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v_isExporting_boxed_2466_; lean_object* v_res_2467_; 
v_isExporting_boxed_2466_ = lean_unbox(v_isExporting_2461_);
v_res_2467_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2460_, v_isExporting_boxed_2466_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object* v_declName_2468_, uint8_t v_isExporting_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2468_, v_isExporting_2469_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object* v_declName_2476_, lean_object* v_isExporting_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v_isExporting_boxed_2483_; lean_object* v_res_2484_; 
v_isExporting_boxed_2483_ = lean_unbox(v_isExporting_2477_);
v_res_2484_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2476_, v_isExporting_boxed_2483_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* v_lhs_2485_, lean_object* v_rhs_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___y_2493_; lean_object* v___x_2510_; uint8_t v_transparency_2511_; uint8_t v___x_2512_; uint8_t v___x_2513_; 
v___x_2510_ = l_Lean_Meta_Context_config(v___y_2487_);
v_transparency_2511_ = lean_ctor_get_uint8(v___x_2510_, 9);
lean_dec_ref(v___x_2510_);
v___x_2512_ = 5;
v___x_2513_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v_keyedConfig_2514_; uint8_t v_trackZetaDelta_2515_; lean_object* v_zetaDeltaSet_2516_; lean_object* v_lctx_2517_; lean_object* v_localInstances_2518_; lean_object* v_defEqCtx_x3f_2519_; lean_object* v_synthPendingDepth_2520_; lean_object* v_customCanUnfoldPredicate_x3f_2521_; uint8_t v_univApprox_2522_; uint8_t v_inTypeClassResolution_2523_; uint8_t v_cacheInferType_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_keyedConfig_2514_ = lean_ctor_get(v___y_2487_, 0);
v_trackZetaDelta_2515_ = lean_ctor_get_uint8(v___y_2487_, sizeof(void*)*7);
v_zetaDeltaSet_2516_ = lean_ctor_get(v___y_2487_, 1);
v_lctx_2517_ = lean_ctor_get(v___y_2487_, 2);
v_localInstances_2518_ = lean_ctor_get(v___y_2487_, 3);
v_defEqCtx_x3f_2519_ = lean_ctor_get(v___y_2487_, 4);
v_synthPendingDepth_2520_ = lean_ctor_get(v___y_2487_, 5);
v_customCanUnfoldPredicate_x3f_2521_ = lean_ctor_get(v___y_2487_, 6);
v_univApprox_2522_ = lean_ctor_get_uint8(v___y_2487_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2523_ = lean_ctor_get_uint8(v___y_2487_, sizeof(void*)*7 + 2);
v_cacheInferType_2524_ = lean_ctor_get_uint8(v___y_2487_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2514_);
v___x_2525_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2512_, v_keyedConfig_2514_);
lean_inc(v_customCanUnfoldPredicate_x3f_2521_);
lean_inc(v_synthPendingDepth_2520_);
lean_inc(v_defEqCtx_x3f_2519_);
lean_inc_ref(v_localInstances_2518_);
lean_inc_ref(v_lctx_2517_);
lean_inc(v_zetaDeltaSet_2516_);
v___x_2526_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v_zetaDeltaSet_2516_);
lean_ctor_set(v___x_2526_, 2, v_lctx_2517_);
lean_ctor_set(v___x_2526_, 3, v_localInstances_2518_);
lean_ctor_set(v___x_2526_, 4, v_defEqCtx_x3f_2519_);
lean_ctor_set(v___x_2526_, 5, v_synthPendingDepth_2520_);
lean_ctor_set(v___x_2526_, 6, v_customCanUnfoldPredicate_x3f_2521_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*7, v_trackZetaDelta_2515_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*7 + 1, v_univApprox_2522_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2523_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*7 + 3, v_cacheInferType_2524_);
v___x_2527_ = l_Lean_Meta_isExprDefEq(v_lhs_2485_, v_rhs_2486_, v___x_2526_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec_ref_known(v___x_2526_, 7);
v___y_2493_ = v___x_2527_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Meta_isExprDefEq(v_lhs_2485_, v_rhs_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
v___y_2493_ = v___x_2528_;
goto v___jp_2492_;
}
v___jp_2492_:
{
if (lean_obj_tag(v___y_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___y_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___y_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2502_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___y_2493_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___y_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* v_lhs_2529_, lean_object* v_rhs_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2529_, v_rhs_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__0));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__2));
v___x_2542_ = l_Lean_stringToMessageData(v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* v_declName_2543_, lean_object* v___f_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2556_; 
lean_inc(v_declName_2543_);
v___x_2556_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_declName_2543_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_n(v_a_2557_, 2);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = 1;
v___x_2559_ = l_Lean_ConstantInfo_value_x3f(v_a_2557_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = l_Lean_ConstantInfo_type(v_a_2557_);
lean_dec(v_a_2557_);
v___x_2562_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v___x_2561_, v_val_2560_, v___y_2548_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; uint8_t v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = lean_unbox(v_a_2563_);
if (v___x_2564_ == 0)
{
lean_dec(v_a_2563_);
lean_dec_ref(v___x_2561_);
lean_dec_ref(v___f_2544_);
lean_dec(v_declName_2543_);
goto v___jp_2553_;
}
else
{
lean_object* v___x_2565_; 
v___x_2565_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v___x_2561_, v___f_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___y_2572_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; uint8_t v___y_2588_; uint8_t v___x_2593_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2593_ = l_Lean_isPrivateName(v_declName_2543_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_unbox(v_a_2563_);
lean_dec(v_a_2563_);
v___y_2588_ = v___x_2594_;
goto v___jp_2587_;
}
else
{
uint8_t v___x_2595_; 
lean_dec(v_a_2563_);
v___x_2595_ = 0;
v___y_2588_ = v___x_2595_;
goto v___jp_2587_;
}
v___jp_2567_:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_unbox(v_a_2566_);
lean_dec(v_a_2566_);
if (v___x_2568_ == 0)
{
goto v___jp_2550_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = l_Lean_defeqAttr;
lean_inc(v_declName_2543_);
v___x_2570_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2569_, v_declName_2543_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_dec_ref_known(v___x_2570_, 1);
goto v___jp_2550_;
}
else
{
lean_dec(v_declName_2543_);
return v___x_2570_;
}
}
}
v___jp_2571_:
{
if (lean_obj_tag(v___y_2572_) == 0)
{
lean_dec_ref_known(v___y_2572_, 1);
goto v___jp_2567_;
}
else
{
lean_dec(v_a_2566_);
lean_dec(v_declName_2543_);
return v___y_2572_;
}
}
v___jp_2573_:
{
if (v___y_2576_ == 0)
{
uint8_t v___x_2577_; 
lean_dec_ref(v___y_2575_);
v___x_2577_ = lean_unbox(v_a_2566_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2578_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__1, &l_Lean_inferDefEqAttr___lam__1___closed__1_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__1);
lean_inc(v_declName_2543_);
v___x_2579_ = l_Lean_MessageData_ofName(v_declName_2543_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__3, &l_Lean_inferDefEqAttr___lam__1___closed__3_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__3);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_Exception_toMessageData(v___y_2574_);
v___x_2584_ = l_Lean_indentD(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2582_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v___x_2585_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
v___y_2572_ = v___x_2586_;
goto v___jp_2571_;
}
else
{
lean_dec_ref(v___y_2574_);
goto v___jp_2567_;
}
}
else
{
lean_dec_ref(v___y_2574_);
v___y_2572_ = v___y_2575_;
goto v___jp_2571_;
}
}
v___jp_2587_:
{
lean_object* v___x_2589_; 
lean_inc(v_declName_2543_);
v___x_2589_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2543_, v___y_2588_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2589_) == 0)
{
v___y_2572_ = v___x_2589_;
goto v___jp_2571_;
}
else
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
v___x_2591_ = l_Lean_Exception_isInterrupt(v_a_2590_);
if (v___x_2591_ == 0)
{
uint8_t v___x_2592_; 
lean_inc(v_a_2590_);
v___x_2592_ = l_Lean_Exception_isRuntime(v_a_2590_);
v___y_2574_ = v_a_2590_;
v___y_2575_ = v___x_2589_;
v___y_2576_ = v___x_2592_;
goto v___jp_2573_;
}
else
{
v___y_2574_ = v_a_2590_;
v___y_2575_ = v___x_2589_;
v___y_2576_ = v___x_2591_;
goto v___jp_2573_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2563_);
lean_dec(v_declName_2543_);
v_a_2596_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2565_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2565_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___x_2561_);
lean_dec_ref(v___f_2544_);
lean_dec(v_declName_2543_);
v_a_2604_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2562_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2562_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_dec(v___x_2559_);
lean_dec(v_a_2557_);
lean_dec_ref(v___f_2544_);
lean_dec(v_declName_2543_);
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___f_2544_);
lean_dec(v_declName_2543_);
v_a_2612_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2556_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2556_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = l_Lean_backwardDefeqAttr;
v___x_2552_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2551_, v_declName_2543_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2552_;
}
v___jp_2553_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object* v_declName_2620_, lean_object* v___f_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2620_, v___f_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object* v_declName_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___f_2635_; lean_object* v___f_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; 
v___f_2635_ = ((lean_object*)(l_Lean_inferDefEqAttr___closed__0));
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2636_, 0, v_declName_2629_);
lean_closure_set(v___f_2636_, 1, v___f_2635_);
v___x_2637_ = 1;
v___x_2638_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___f_2636_, v___x_2637_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object* v_declName_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_inferDefEqAttr(v_declName_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_2646_, lean_object* v_attrName_2647_, lean_object* v_declName_2648_, lean_object* v_asyncPrefix_x3f_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_2647_, v_declName_2648_, v_asyncPrefix_x3f_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2656_, lean_object* v_attrName_2657_, lean_object* v_declName_2658_, lean_object* v_asyncPrefix_x3f_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_2656_, v_attrName_2657_, v_declName_2658_, v_asyncPrefix_x3f_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object* v_00_u03b1_2666_, lean_object* v_attrName_2667_, lean_object* v_declName_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_2667_, v_declName_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_attrName_2676_, lean_object* v_declName_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_2675_, v_attrName_2676_, v_declName_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object* v_00_u03b1_2684_, lean_object* v_constName_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_constName_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_2692_, v_constName_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object* v_00_u03b1_2700_, lean_object* v_ref_2701_, lean_object* v_constName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2701_, v_constName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_ref_2710_, lean_object* v_constName_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_2709_, v_ref_2710_, v_constName_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v_ref_2710_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object* v_00_u03b1_2718_, lean_object* v_ref_2719_, lean_object* v_msg_2720_, lean_object* v_declHint_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2719_, v_msg_2720_, v_declHint_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_ref_2729_, lean_object* v_msg_2730_, lean_object* v_declHint_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_2728_, v_ref_2729_, v_msg_2730_, v_declHint_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v_ref_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(lean_object* v_msg_2738_, lean_object* v_declHint_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_2738_, v_declHint_2739_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___boxed(lean_object* v_msg_2746_, lean_object* v_declHint_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(v_msg_2746_, v_declHint_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_2754_, lean_object* v_ref_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2755_, v_msg_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_ref_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_2763_, v_ref_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v_ref_2764_);
return v_res_2771_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
