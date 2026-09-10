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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object* v_e1_127_, lean_object* v_e2_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_192_; lean_object* v_toCold_193_; lean_object* v_currRecDepth_194_; lean_object* v_ref_195_; uint8_t v_suppressElabErrors_196_; lean_object* v_fileName_197_; lean_object* v_fileMap_198_; lean_object* v_options_199_; lean_object* v_currNamespace_200_; lean_object* v_openDecls_201_; lean_object* v_initHeartbeats_202_; lean_object* v_maxHeartbeats_203_; lean_object* v_quotContext_204_; lean_object* v_currMacroScope_205_; lean_object* v_cancelTk_x3f_206_; lean_object* v_inheritedTraceOptions_207_; lean_object* v_env_208_; uint8_t v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v_fileName_216_; lean_object* v_fileMap_217_; lean_object* v_currNamespace_218_; lean_object* v_openDecls_219_; lean_object* v_initHeartbeats_220_; lean_object* v_maxHeartbeats_221_; lean_object* v_quotContext_222_; lean_object* v_currMacroScope_223_; lean_object* v_cancelTk_x3f_224_; lean_object* v_inheritedTraceOptions_225_; lean_object* v_currRecDepth_226_; lean_object* v_ref_227_; uint8_t v_suppressElabErrors_228_; lean_object* v___y_229_; uint8_t v___y_253_; uint8_t v___x_274_; 
v___x_192_ = lean_st_ref_get(v_a_132_);
v_toCold_193_ = lean_ctor_get(v_a_131_, 0);
v_currRecDepth_194_ = lean_ctor_get(v_a_131_, 1);
v_ref_195_ = lean_ctor_get(v_a_131_, 2);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v_a_131_, sizeof(void*)*3 + 1);
v_fileName_197_ = lean_ctor_get(v_toCold_193_, 0);
v_fileMap_198_ = lean_ctor_get(v_toCold_193_, 1);
v_options_199_ = lean_ctor_get(v_toCold_193_, 2);
v_currNamespace_200_ = lean_ctor_get(v_toCold_193_, 4);
v_openDecls_201_ = lean_ctor_get(v_toCold_193_, 5);
v_initHeartbeats_202_ = lean_ctor_get(v_toCold_193_, 6);
v_maxHeartbeats_203_ = lean_ctor_get(v_toCold_193_, 7);
v_quotContext_204_ = lean_ctor_get(v_toCold_193_, 8);
v_currMacroScope_205_ = lean_ctor_get(v_toCold_193_, 9);
v_cancelTk_x3f_206_ = lean_ctor_get(v_toCold_193_, 10);
v_inheritedTraceOptions_207_ = lean_ctor_get(v_toCold_193_, 11);
v_env_208_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_208_);
lean_dec(v___x_192_);
v___x_209_ = 1;
v___x_210_ = l_Lean_Meta_smartUnfolding;
v___x_211_ = 0;
lean_inc_ref(v_options_199_);
v___x_212_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_options_199_, v___x_210_, v___x_211_);
v___x_213_ = l_Lean_diagnostics;
v___x_214_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v___x_212_, v___x_213_);
v___x_274_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_208_);
lean_dec_ref(v_env_208_);
if (v___x_214_ == 0)
{
if (v___x_274_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_207_);
lean_inc(v_cancelTk_x3f_206_);
lean_inc(v_currMacroScope_205_);
lean_inc(v_quotContext_204_);
lean_inc(v_maxHeartbeats_203_);
lean_inc(v_initHeartbeats_202_);
lean_inc(v_openDecls_201_);
lean_inc(v_currNamespace_200_);
lean_inc_ref(v_fileMap_198_);
lean_inc_ref(v_fileName_197_);
v_fileName_216_ = v_fileName_197_;
v_fileMap_217_ = v_fileMap_198_;
v_currNamespace_218_ = v_currNamespace_200_;
v_openDecls_219_ = v_openDecls_201_;
v_initHeartbeats_220_ = v_initHeartbeats_202_;
v_maxHeartbeats_221_ = v_maxHeartbeats_203_;
v_quotContext_222_ = v_quotContext_204_;
v_currMacroScope_223_ = v_currMacroScope_205_;
v_cancelTk_x3f_224_ = v_cancelTk_x3f_206_;
v_inheritedTraceOptions_225_ = v_inheritedTraceOptions_207_;
v_currRecDepth_226_ = v_currRecDepth_194_;
v_ref_227_ = v_ref_195_;
v_suppressElabErrors_228_ = v_suppressElabErrors_196_;
v___y_229_ = v_a_132_;
goto v___jp_215_;
}
else
{
v___y_253_ = v___x_214_;
goto v___jp_252_;
}
}
else
{
v___y_253_ = v___x_274_;
goto v___jp_252_;
}
v___jp_134_:
{
if (lean_obj_tag(v___y_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___y_135_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___y_135_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___y_135_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___y_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___y_135_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___y_135_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___y_135_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___y_135_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
v___jp_152_:
{
if (lean_obj_tag(v___y_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_183_; 
v_a_156_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_183_ == 0)
{
v___x_158_ = v___y_155_;
v_isShared_159_ = v_isSharedCheck_183_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___y_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_183_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
uint8_t v___x_160_; 
v___x_160_ = lean_unbox(v_a_156_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v_transparency_162_; uint8_t v___x_163_; uint8_t v___x_164_; 
lean_del_object(v___x_158_);
lean_dec(v_a_156_);
v___x_161_ = l_Lean_Meta_Context_config(v_a_129_);
v_transparency_162_ = lean_ctor_get_uint8(v___x_161_, 9);
lean_dec_ref(v___x_161_);
v___x_163_ = 0;
v___x_164_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v_keyedConfig_165_; uint8_t v_trackZetaDelta_166_; lean_object* v_zetaDeltaSet_167_; lean_object* v_lctx_168_; lean_object* v_localInstances_169_; lean_object* v_defEqCtx_x3f_170_; lean_object* v_synthPendingDepth_171_; lean_object* v_customCanUnfoldPredicate_x3f_172_; uint8_t v_univApprox_173_; uint8_t v_inTypeClassResolution_174_; uint8_t v_cacheInferType_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_keyedConfig_165_ = lean_ctor_get(v_a_129_, 0);
v_trackZetaDelta_166_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7);
v_zetaDeltaSet_167_ = lean_ctor_get(v_a_129_, 1);
v_lctx_168_ = lean_ctor_get(v_a_129_, 2);
v_localInstances_169_ = lean_ctor_get(v_a_129_, 3);
v_defEqCtx_x3f_170_ = lean_ctor_get(v_a_129_, 4);
v_synthPendingDepth_171_ = lean_ctor_get(v_a_129_, 5);
v_customCanUnfoldPredicate_x3f_172_ = lean_ctor_get(v_a_129_, 6);
v_univApprox_173_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_174_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 2);
v_cacheInferType_175_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_165_);
v___x_176_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_163_, v_keyedConfig_165_);
lean_inc(v_customCanUnfoldPredicate_x3f_172_);
lean_inc(v_synthPendingDepth_171_);
lean_inc(v_defEqCtx_x3f_170_);
lean_inc_ref(v_localInstances_169_);
lean_inc_ref(v_lctx_168_);
lean_inc(v_zetaDeltaSet_167_);
v___x_177_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_zetaDeltaSet_167_);
lean_ctor_set(v___x_177_, 2, v_lctx_168_);
lean_ctor_set(v___x_177_, 3, v_localInstances_169_);
lean_ctor_set(v___x_177_, 4, v_defEqCtx_x3f_170_);
lean_ctor_set(v___x_177_, 5, v_synthPendingDepth_171_);
lean_ctor_set(v___x_177_, 6, v_customCanUnfoldPredicate_x3f_172_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*7, v_trackZetaDelta_166_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*7 + 1, v_univApprox_173_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*7 + 2, v_inTypeClassResolution_174_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*7 + 3, v_cacheInferType_175_);
v___x_178_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v___x_177_, v_a_130_, v___y_153_, v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec_ref_known(v___x_177_, 7);
v___y_135_ = v___x_178_;
goto v___jp_134_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v_a_129_, v_a_130_, v___y_153_, v___y_154_);
lean_dec_ref(v___y_153_);
v___y_135_ = v___x_179_;
goto v___jp_134_;
}
}
else
{
lean_object* v___x_181_; 
lean_dec_ref(v___y_153_);
lean_dec_ref(v_e2_128_);
lean_dec_ref(v_e1_127_);
if (v_isShared_159_ == 0)
{
v___x_181_ = v___x_158_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_156_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v___y_153_);
lean_dec_ref(v_e2_128_);
lean_dec_ref(v_e1_127_);
v_a_184_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___y_155_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___y_155_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
v___jp_215_:
{
lean_object* v___x_230_; uint8_t v_transparency_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_230_ = l_Lean_Meta_Context_config(v_a_129_);
v_transparency_231_ = lean_ctor_get_uint8(v___x_230_, 9);
lean_dec_ref(v___x_230_);
v___x_232_ = l_Lean_maxRecDepth;
v___x_233_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(v___x_212_, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_234_, 0, v_fileName_216_);
lean_ctor_set(v___x_234_, 1, v_fileMap_217_);
lean_ctor_set(v___x_234_, 2, v___x_212_);
lean_ctor_set(v___x_234_, 3, v___x_233_);
lean_ctor_set(v___x_234_, 4, v_currNamespace_218_);
lean_ctor_set(v___x_234_, 5, v_openDecls_219_);
lean_ctor_set(v___x_234_, 6, v_initHeartbeats_220_);
lean_ctor_set(v___x_234_, 7, v_maxHeartbeats_221_);
lean_ctor_set(v___x_234_, 8, v_quotContext_222_);
lean_ctor_set(v___x_234_, 9, v_currMacroScope_223_);
lean_ctor_set(v___x_234_, 10, v_cancelTk_x3f_224_);
lean_ctor_set(v___x_234_, 11, v_inheritedTraceOptions_225_);
lean_inc(v_ref_227_);
lean_inc(v_currRecDepth_226_);
v___x_235_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_currRecDepth_226_);
lean_ctor_set(v___x_235_, 2, v_ref_227_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3, v___x_214_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 1, v_suppressElabErrors_228_);
v___x_236_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_231_, v___x_209_);
if (v___x_236_ == 0)
{
lean_object* v_keyedConfig_237_; uint8_t v_trackZetaDelta_238_; lean_object* v_zetaDeltaSet_239_; lean_object* v_lctx_240_; lean_object* v_localInstances_241_; lean_object* v_defEqCtx_x3f_242_; lean_object* v_synthPendingDepth_243_; lean_object* v_customCanUnfoldPredicate_x3f_244_; uint8_t v_univApprox_245_; uint8_t v_inTypeClassResolution_246_; uint8_t v_cacheInferType_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_keyedConfig_237_ = lean_ctor_get(v_a_129_, 0);
v_trackZetaDelta_238_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7);
v_zetaDeltaSet_239_ = lean_ctor_get(v_a_129_, 1);
v_lctx_240_ = lean_ctor_get(v_a_129_, 2);
v_localInstances_241_ = lean_ctor_get(v_a_129_, 3);
v_defEqCtx_x3f_242_ = lean_ctor_get(v_a_129_, 4);
v_synthPendingDepth_243_ = lean_ctor_get(v_a_129_, 5);
v_customCanUnfoldPredicate_x3f_244_ = lean_ctor_get(v_a_129_, 6);
v_univApprox_245_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_246_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 2);
v_cacheInferType_247_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_237_);
v___x_248_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_209_, v_keyedConfig_237_);
lean_inc(v_customCanUnfoldPredicate_x3f_244_);
lean_inc(v_synthPendingDepth_243_);
lean_inc(v_defEqCtx_x3f_242_);
lean_inc_ref(v_localInstances_241_);
lean_inc_ref(v_lctx_240_);
lean_inc(v_zetaDeltaSet_239_);
v___x_249_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_zetaDeltaSet_239_);
lean_ctor_set(v___x_249_, 2, v_lctx_240_);
lean_ctor_set(v___x_249_, 3, v_localInstances_241_);
lean_ctor_set(v___x_249_, 4, v_defEqCtx_x3f_242_);
lean_ctor_set(v___x_249_, 5, v_synthPendingDepth_243_);
lean_ctor_set(v___x_249_, 6, v_customCanUnfoldPredicate_x3f_244_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*7, v_trackZetaDelta_238_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*7 + 1, v_univApprox_245_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*7 + 2, v_inTypeClassResolution_246_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*7 + 3, v_cacheInferType_247_);
lean_inc_ref(v_e2_128_);
lean_inc_ref(v_e1_127_);
v___x_250_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v___x_249_, v_a_130_, v___x_235_, v___y_229_);
lean_dec_ref_known(v___x_249_, 7);
v___y_153_ = v___x_235_;
v___y_154_ = v___y_229_;
v___y_155_ = v___x_250_;
goto v___jp_152_;
}
else
{
lean_object* v___x_251_; 
lean_inc_ref(v_e2_128_);
lean_inc_ref(v_e1_127_);
v___x_251_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v_a_129_, v_a_130_, v___x_235_, v___y_229_);
v___y_153_ = v___x_235_;
v___y_154_ = v___y_229_;
v___y_155_ = v___x_251_;
goto v___jp_152_;
}
}
v___jp_252_:
{
if (v___y_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_env_255_; lean_object* v_nextMacroScope_256_; lean_object* v_ngen_257_; lean_object* v_auxDeclNGen_258_; lean_object* v_traceState_259_; lean_object* v_messages_260_; lean_object* v_infoState_261_; lean_object* v_snapshotTasks_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_272_; 
v___x_254_ = lean_st_ref_take(v_a_132_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
v_nextMacroScope_256_ = lean_ctor_get(v___x_254_, 1);
v_ngen_257_ = lean_ctor_get(v___x_254_, 2);
v_auxDeclNGen_258_ = lean_ctor_get(v___x_254_, 3);
v_traceState_259_ = lean_ctor_get(v___x_254_, 4);
v_messages_260_ = lean_ctor_get(v___x_254_, 6);
v_infoState_261_ = lean_ctor_get(v___x_254_, 7);
v_snapshotTasks_262_ = lean_ctor_get(v___x_254_, 8);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_254_, 5);
lean_dec(v_unused_273_);
v___x_264_ = v___x_254_;
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snapshotTasks_262_);
lean_inc(v_infoState_261_);
lean_inc(v_messages_260_);
lean_inc(v_traceState_259_);
lean_inc(v_auxDeclNGen_258_);
lean_inc(v_ngen_257_);
lean_inc(v_nextMacroScope_256_);
lean_inc(v_env_255_);
lean_dec(v___x_254_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = l_Lean_Kernel_enableDiag(v_env_255_, v___x_214_);
v___x_267_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 5, v___x_267_);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_nextMacroScope_256_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_ngen_257_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_auxDeclNGen_258_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_traceState_259_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_messages_260_);
lean_ctor_set(v_reuseFailAlloc_271_, 7, v_infoState_261_);
lean_ctor_set(v_reuseFailAlloc_271_, 8, v_snapshotTasks_262_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; 
v___x_270_ = lean_st_ref_put(v_a_132_, v___x_269_);
lean_inc_ref(v_inheritedTraceOptions_207_);
lean_inc(v_cancelTk_x3f_206_);
lean_inc(v_currMacroScope_205_);
lean_inc(v_quotContext_204_);
lean_inc(v_maxHeartbeats_203_);
lean_inc(v_initHeartbeats_202_);
lean_inc(v_openDecls_201_);
lean_inc(v_currNamespace_200_);
lean_inc_ref(v_fileMap_198_);
lean_inc_ref(v_fileName_197_);
v_fileName_216_ = v_fileName_197_;
v_fileMap_217_ = v_fileMap_198_;
v_currNamespace_218_ = v_currNamespace_200_;
v_openDecls_219_ = v_openDecls_201_;
v_initHeartbeats_220_ = v_initHeartbeats_202_;
v_maxHeartbeats_221_ = v_maxHeartbeats_203_;
v_quotContext_222_ = v_quotContext_204_;
v_currMacroScope_223_ = v_currMacroScope_205_;
v_cancelTk_x3f_224_ = v_cancelTk_x3f_206_;
v_inheritedTraceOptions_225_ = v_inheritedTraceOptions_207_;
v_currRecDepth_226_ = v_currRecDepth_194_;
v_ref_227_ = v_ref_195_;
v_suppressElabErrors_228_ = v_suppressElabErrors_196_;
v___y_229_ = v_a_132_;
goto v___jp_215_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_207_);
lean_inc(v_cancelTk_x3f_206_);
lean_inc(v_currMacroScope_205_);
lean_inc(v_quotContext_204_);
lean_inc(v_maxHeartbeats_203_);
lean_inc(v_initHeartbeats_202_);
lean_inc(v_openDecls_201_);
lean_inc(v_currNamespace_200_);
lean_inc_ref(v_fileMap_198_);
lean_inc_ref(v_fileName_197_);
v_fileName_216_ = v_fileName_197_;
v_fileMap_217_ = v_fileMap_198_;
v_currNamespace_218_ = v_currNamespace_200_;
v_openDecls_219_ = v_openDecls_201_;
v_initHeartbeats_220_ = v_initHeartbeats_202_;
v_maxHeartbeats_221_ = v_maxHeartbeats_203_;
v_quotContext_222_ = v_quotContext_204_;
v_currMacroScope_223_ = v_currMacroScope_205_;
v_cancelTk_x3f_224_ = v_cancelTk_x3f_206_;
v_inheritedTraceOptions_225_ = v_inheritedTraceOptions_207_;
v_currRecDepth_226_ = v_currRecDepth_194_;
v_ref_227_ = v_ref_195_;
v_suppressElabErrors_228_ = v_suppressElabErrors_196_;
v___y_229_ = v_a_132_;
goto v___jp_215_;
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
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_traceState_556_; lean_object* v_messages_557_; lean_object* v_infoState_558_; lean_object* v_snapshotTasks_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_584_; 
v___x_551_ = lean_st_ref_take(v___y_544_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_551_, 1);
v_ngen_554_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_551_, 3);
v_traceState_556_ = lean_ctor_get(v___x_551_, 4);
v_messages_557_ = lean_ctor_get(v___x_551_, 6);
v_infoState_558_ = lean_ctor_get(v___x_551_, 7);
v_snapshotTasks_559_ = lean_ctor_get(v___x_551_, 8);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_551_, 5);
lean_dec(v_unused_585_);
v___x_561_ = v___x_551_;
v_isShared_562_ = v_isSharedCheck_584_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snapshotTasks_559_);
lean_inc(v_infoState_558_);
lean_inc(v_messages_557_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_551_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_584_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Environment_setExporting(v_env_552_, v_isExporting_545_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 5, v___x_546_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_traceState_556_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_messages_557_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_infoState_558_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_snapshotTasks_559_);
v___x_565_ = v_reuseFailAlloc_583_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_mctx_568_; lean_object* v_zetaDeltaFVarIds_569_; lean_object* v_postponed_570_; lean_object* v_diag_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_581_; 
v___x_566_ = lean_st_ref_put(v___y_544_, v___x_565_);
v___x_567_ = lean_st_ref_take(v___y_547_);
v_mctx_568_ = lean_ctor_get(v___x_567_, 0);
v_zetaDeltaFVarIds_569_ = lean_ctor_get(v___x_567_, 2);
v_postponed_570_ = lean_ctor_get(v___x_567_, 3);
v_diag_571_ = lean_ctor_get(v___x_567_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_567_, 1);
lean_dec(v_unused_582_);
v___x_573_ = v___x_567_;
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_diag_571_);
lean_inc(v_postponed_570_);
lean_inc(v_zetaDeltaFVarIds_569_);
lean_inc(v_mctx_568_);
lean_dec(v___x_567_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_548_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_mctx_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_zetaDeltaFVarIds_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_postponed_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_diag_571_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_st_ref_put(v___y_547_, v___x_576_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___y_586_, lean_object* v_isExporting_587_, lean_object* v___x_588_, lean_object* v___y_589_, lean_object* v___x_590_, lean_object* v_a_x3f_591_, lean_object* v___y_592_){
_start:
{
uint8_t v_isExporting_boxed_593_; lean_object* v_res_594_; 
v_isExporting_boxed_593_ = lean_unbox(v_isExporting_587_);
v_res_594_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_586_, v_isExporting_boxed_593_, v___x_588_, v___y_589_, v___x_590_, v_a_x3f_591_);
lean_dec(v_a_x3f_591_);
lean_dec(v___y_589_);
lean_dec(v___y_586_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_596_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
lean_ctor_set(v___x_596_, 4, v___x_595_);
lean_ctor_set(v___x_596_, 5, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object* v_x_597_, uint8_t v_isExporting_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_env_605_; lean_object* v___x_606_; uint8_t v_isModule_607_; 
v___x_604_ = lean_st_ref_get(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v___x_606_ = l_Lean_Environment_header(v_env_605_);
v_isModule_607_ = lean_ctor_get_uint8(v___x_606_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_606_);
if (v_isModule_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_env_605_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v___x_608_ = lean_apply_5(v_x_597_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
return v___x_608_;
}
else
{
uint8_t v_isExporting_609_; 
v_isExporting_609_ = lean_ctor_get_uint8(v_env_605_, sizeof(void*)*8);
lean_dec_ref(v_env_605_);
if (v_isExporting_598_ == 0)
{
if (v_isExporting_609_ == 0)
{
lean_object* v___x_675_; 
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v___x_675_ = lean_apply_5(v_x_597_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
return v___x_675_;
}
else
{
goto v___jp_610_;
}
}
else
{
if (v_isExporting_609_ == 0)
{
goto v___jp_610_;
}
else
{
lean_object* v___x_676_; 
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v___x_676_ = lean_apply_5(v_x_597_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
return v___x_676_;
}
}
v___jp_610_:
{
lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v_nextMacroScope_613_; lean_object* v_ngen_614_; lean_object* v_auxDeclNGen_615_; lean_object* v_traceState_616_; lean_object* v_messages_617_; lean_object* v_infoState_618_; lean_object* v_snapshotTasks_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_673_; 
v___x_611_ = lean_st_ref_take(v___y_602_);
v_env_612_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_613_ = lean_ctor_get(v___x_611_, 1);
v_ngen_614_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_615_ = lean_ctor_get(v___x_611_, 3);
v_traceState_616_ = lean_ctor_get(v___x_611_, 4);
v_messages_617_ = lean_ctor_get(v___x_611_, 6);
v_infoState_618_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_619_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_611_, 5);
lean_dec(v_unused_674_);
v___x_621_ = v___x_611_;
v_isShared_622_ = v_isSharedCheck_673_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snapshotTasks_619_);
lean_inc(v_infoState_618_);
lean_inc(v_messages_617_);
lean_inc(v_traceState_616_);
lean_inc(v_auxDeclNGen_615_);
lean_inc(v_ngen_614_);
lean_inc(v_nextMacroScope_613_);
lean_inc(v_env_612_);
lean_dec(v___x_611_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_673_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_623_ = l_Lean_Environment_setExporting(v_env_612_, v_isExporting_598_);
v___x_624_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 5, v___x_624_);
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_nextMacroScope_613_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ngen_614_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_auxDeclNGen_615_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_traceState_616_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v_messages_617_);
lean_ctor_set(v_reuseFailAlloc_672_, 7, v_infoState_618_);
lean_ctor_set(v_reuseFailAlloc_672_, 8, v_snapshotTasks_619_);
v___x_626_ = v_reuseFailAlloc_672_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_mctx_629_; lean_object* v_zetaDeltaFVarIds_630_; lean_object* v_postponed_631_; lean_object* v_diag_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_670_; 
v___x_627_ = lean_st_ref_put(v___y_602_, v___x_626_);
v___x_628_ = lean_st_ref_take(v___y_600_);
v_mctx_629_ = lean_ctor_get(v___x_628_, 0);
v_zetaDeltaFVarIds_630_ = lean_ctor_get(v___x_628_, 2);
v_postponed_631_ = lean_ctor_get(v___x_628_, 3);
v_diag_632_ = lean_ctor_get(v___x_628_, 4);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_628_, 1);
lean_dec(v_unused_671_);
v___x_634_ = v___x_628_;
v_isShared_635_ = v_isSharedCheck_670_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_diag_632_);
lean_inc(v_postponed_631_);
lean_inc(v_zetaDeltaFVarIds_630_);
lean_inc(v_mctx_629_);
lean_dec(v___x_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_670_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_mctx_629_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_zetaDeltaFVarIds_630_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_postponed_631_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_diag_632_);
v___x_638_ = v_reuseFailAlloc_669_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v_r_640_; 
v___x_639_ = lean_st_ref_put(v___y_600_, v___x_638_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v_r_640_ = lean_apply_5(v_x_597_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
if (lean_obj_tag(v_r_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_657_; 
v_a_641_ = lean_ctor_get(v_r_640_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_r_640_);
if (v_isSharedCheck_657_ == 0)
{
v___x_643_ = v_r_640_;
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v_r_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
lean_inc(v_a_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 1);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_656_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v___x_647_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_602_, v_isExporting_609_, v___x_624_, v___y_600_, v___x_636_, v___x_646_);
lean_dec_ref(v___x_646_);
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
lean_ctor_set(v___x_649_, 0, v_a_641_);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_641_);
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
else
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_658_ = lean_ctor_get(v_r_640_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_r_640_, 1);
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_602_, v_isExporting_609_, v___x_624_, v___y_600_, v___x_636_, v___x_659_);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v___x_660_, 0);
lean_dec(v_unused_668_);
v___x_662_ = v___x_660_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_dec(v___x_660_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v_a_658_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_658_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_677_, lean_object* v_isExporting_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_isExporting_boxed_684_; lean_object* v_res_685_; 
v_isExporting_boxed_684_ = lean_unbox(v_isExporting_678_);
v_res_685_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_677_, v_isExporting_boxed_684_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object* v_x_686_, uint8_t v_when_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
if (v_when_687_ == 0)
{
lean_object* v___x_693_; 
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
v___x_693_ = lean_apply_5(v_x_686_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, lean_box(0));
return v___x_693_;
}
else
{
uint8_t v___x_694_; lean_object* v___x_695_; 
v___x_694_ = 0;
v___x_695_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_686_, v___x_694_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object* v_x_696_, lean_object* v_when_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_when_boxed_703_; lean_object* v_res_704_; 
v_when_boxed_703_ = lean_unbox(v_when_697_);
v_res_704_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_696_, v_when_boxed_703_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_704_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__0));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__2));
v___x_710_ = l_Lean_stringToMessageData(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__4));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__5, &l_Lean_validateDefEqAttr___lam__0___closed__5_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__5);
v___x_715_ = l_Lean_MessageData_note(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* v_lhs_716_, lean_object* v_rhs_717_, uint8_t v___x_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_lhs_716_, v_rhs_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_774_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_774_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_774_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_774_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_773_; 
v_fst_729_ = lean_ctor_get(v_a_725_, 0);
v_snd_730_ = lean_ctor_get(v_a_725_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_773_ == 0)
{
v___x_732_ = v_a_725_;
v_isShared_733_ = v_isSharedCheck_773_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_729_);
lean_dec(v_a_725_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_773_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v_env_735_; uint8_t v_isExporting_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_734_ = lean_st_ref_get(v___y_722_);
v_env_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_env_735_);
lean_dec(v___x_734_);
v_isExporting_736_ = lean_ctor_get_uint8(v_env_735_, sizeof(void*)*8);
lean_dec_ref(v_env_735_);
v___x_737_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__1, &l_Lean_validateDefEqAttr___lam__0___closed__1_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__1);
lean_inc(v_fst_729_);
v___x_738_ = l_Lean_indentExpr(v_fst_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 7);
lean_ctor_set(v___x_732_, 1, v___x_738_);
lean_ctor_set(v___x_732_, 0, v___x_737_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_772_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__3, &l_Lean_validateDefEqAttr___lam__0___closed__3_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__3);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
lean_inc(v_snd_730_);
v___x_743_ = l_Lean_indentExpr(v_snd_730_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
if (v_isExporting_736_ == 0)
{
lean_object* v___x_746_; 
lean_dec(v_snd_730_);
lean_dec(v_fst_729_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_744_);
v___x_746_ = v___x_727_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_del_object(v___x_727_);
v___x_748_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed), 7, 2);
lean_closure_set(v___x_748_, 0, v_fst_729_);
lean_closure_set(v___x_748_, 1, v_snd_730_);
v___x_749_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___x_748_, v___x_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_763_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_763_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = lean_unbox(v_a_750_);
lean_dec(v_a_750_);
if (v___x_754_ == 0)
{
lean_object* v___x_756_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_744_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_744_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__6, &l_Lean_validateDefEqAttr___lam__0___closed__6_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__6);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_744_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_759_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
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
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref_known(v___x_744_, 2);
v_a_764_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_749_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_749_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
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
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_724_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_724_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object* v_lhs_783_, lean_object* v_rhs_784_, lean_object* v___x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v___x_6340__boxed_791_; lean_object* v_res_792_; 
v___x_6340__boxed_791_ = lean_unbox(v___x_785_);
v_res_792_ = l_Lean_validateDefEqAttr___lam__0(v_lhs_783_, v_rhs_784_, v___x_6340__boxed_791_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* v_lhs_793_, lean_object* v_rhs_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
lean_inc_ref(v_rhs_794_);
lean_inc_ref(v_lhs_793_);
v___x_800_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_lhs_793_, v_rhs_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_819_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_819_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_819_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint8_t v___x_805_; 
v___x_805_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_803_);
v___x_806_ = 1;
v___x_807_ = lean_box(v___x_806_);
lean_inc_ref(v_rhs_794_);
lean_inc_ref(v_lhs_793_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_808_, 0, v_lhs_793_);
lean_closure_set(v___f_808_, 1, v_rhs_794_);
lean_closure_set(v___f_808_, 2, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_809_);
v___x_811_ = lean_array_push(v___x_810_, v_lhs_793_);
v___x_812_ = lean_array_push(v___x_811_, v_rhs_794_);
v___x_813_ = l_Lean_MessageData_ofLazyM(v___f_808_, v___x_812_);
v___x_814_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_813_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v_rhs_794_);
lean_dec_ref(v_lhs_793_);
v___x_815_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_815_);
v___x_817_ = v___x_803_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
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
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_rhs_794_);
lean_dec_ref(v_lhs_793_);
v_a_820_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_800_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_800_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* v_lhs_828_, lean_object* v_rhs_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_828_, v_rhs_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
lean_ctor_set(v___x_841_, 2, v___x_840_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
lean_ctor_set(v___x_841_, 4, v___x_839_);
lean_ctor_set(v___x_841_, 5, v___x_839_);
lean_ctor_set(v___x_841_, 6, v___x_839_);
lean_ctor_set(v___x_841_, 7, v___x_839_);
lean_ctor_set(v___x_841_, 8, v___x_839_);
lean_ctor_set(v___x_841_, 9, v___x_839_);
lean_ctor_set(v___x_841_, 10, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(32u);
v___x_843_ = lean_mk_empty_array_with_capacity(v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_845_ = ((size_t)5ULL);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_unsigned_to_nat(32u);
v___x_848_ = lean_mk_empty_array_with_capacity(v___x_847_);
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_850_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
lean_ctor_set(v___x_850_, 2, v___x_846_);
lean_ctor_set(v___x_850_, 3, v___x_846_);
lean_ctor_set_usize(v___x_850_, 4, v___x_845_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_851_ = lean_box(1);
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_851_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_869_ = l_Lean_stringToMessageData(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_876_, lean_object* v_declHint_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_env_881_; uint8_t v___x_882_; 
v___x_880_ = lean_st_ref_get(v___y_878_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
lean_dec(v___x_880_);
v___x_882_ = l_Lean_Name_isAnonymous(v_declHint_877_);
if (v___x_882_ == 0)
{
uint8_t v_isExporting_883_; 
v_isExporting_883_ = lean_ctor_get_uint8(v_env_881_, sizeof(void*)*8);
if (v_isExporting_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v_env_881_);
lean_dec(v_declHint_877_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_msg_876_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; uint8_t v___x_886_; 
lean_inc_ref(v_env_881_);
v___x_885_ = l_Lean_Environment_setExporting(v_env_881_, v___x_882_);
lean_inc(v_declHint_877_);
lean_inc_ref(v___x_885_);
v___x_886_ = l_Lean_Environment_contains(v___x_885_, v_declHint_877_, v_isExporting_883_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v_env_881_);
lean_dec(v_declHint_877_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_msg_876_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_c_893_; lean_object* v___x_894_; 
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_890_ = l_Lean_Options_empty;
v___x_891_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_891_, 0, v___x_885_);
lean_ctor_set(v___x_891_, 1, v___x_888_);
lean_ctor_set(v___x_891_, 2, v___x_889_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
lean_inc(v_declHint_877_);
v___x_892_ = l_Lean_MessageData_ofConstName(v_declHint_877_, v___x_882_);
v_c_893_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_893_, 0, v___x_891_);
lean_ctor_set(v_c_893_, 1, v___x_892_);
v___x_894_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_881_, v_declHint_877_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_env_881_);
lean_dec(v_declHint_877_);
v___x_895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v_c_893_);
v___x_897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_MessageData_note(v___x_898_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v_msg_876_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_937_; 
v_val_902_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_937_ == 0)
{
v___x_904_ = v___x_894_;
v_isShared_905_ = v_isSharedCheck_937_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_dec(v___x_894_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_937_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_mod_909_; uint8_t v___x_910_; 
v___x_906_ = lean_box(0);
v___x_907_ = l_Lean_Environment_header(v_env_881_);
lean_dec_ref(v_env_881_);
v___x_908_ = l_Lean_EnvironmentHeader_moduleNames(v___x_907_);
v_mod_909_ = lean_array_get(v___x_906_, v___x_908_, v_val_902_);
lean_dec(v_val_902_);
lean_dec_ref(v___x_908_);
v___x_910_ = l_Lean_isPrivateName(v_declHint_877_);
lean_dec(v_declHint_877_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_c_893_);
v___x_913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_MessageData_ofName(v_mod_909_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_MessageData_note(v___x_918_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v_msg_876_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 0);
lean_ctor_set(v___x_904_, 0, v___x_920_);
v___x_922_ = v___x_904_;
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
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_924_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_c_893_);
v___x_926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_MessageData_ofName(v_mod_909_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_MessageData_note(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v_msg_876_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 0);
lean_ctor_set(v___x_904_, 0, v___x_933_);
v___x_935_ = v___x_904_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_938_; 
lean_dec_ref(v_env_881_);
lean_dec(v_declHint_877_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_msg_876_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_939_, lean_object* v_declHint_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_939_, v_declHint_940_, v___y_941_);
lean_dec(v___y_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_944_, lean_object* v_declHint_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v___x_949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_944_, v_declHint_945_, v___y_947_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_954_ = l_Lean_unknownIdentifierMessageTag;
v___x_955_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_a_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_960_, lean_object* v_declHint_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_960_, v_declHint_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_toCold_971_; lean_object* v_env_972_; lean_object* v_options_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_toCold_971_ = lean_ctor_get(v___y_967_, 0);
v_env_972_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_972_);
lean_dec(v___x_970_);
v_options_973_ = lean_ctor_get(v_toCold_971_, 2);
v___x_974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_975_ = lean_unsigned_to_nat(32u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
lean_dec_ref(v___x_976_);
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_973_);
v___x_978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_978_, 0, v_env_972_);
lean_ctor_set(v___x_978_, 1, v___x_974_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
lean_ctor_set(v___x_978_, 3, v_options_973_);
v___x_979_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_msgData_966_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_ref_990_; lean_object* v___x_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1000_; 
v_ref_990_ = lean_ctor_get(v___y_987_, 2);
v___x_991_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_986_, v___y_987_, v___y_988_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_inc(v_ref_990_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v_ref_990_);
lean_ctor_set(v___x_996_, 1, v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 1);
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1006_, lean_object* v_msg_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_toCold_1011_; lean_object* v_currRecDepth_1012_; lean_object* v_ref_1013_; uint8_t v_diag_1014_; uint8_t v_suppressElabErrors_1015_; lean_object* v_ref_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_toCold_1011_ = lean_ctor_get(v___y_1008_, 0);
v_currRecDepth_1012_ = lean_ctor_get(v___y_1008_, 1);
v_ref_1013_ = lean_ctor_get(v___y_1008_, 2);
v_diag_1014_ = lean_ctor_get_uint8(v___y_1008_, sizeof(void*)*3);
v_suppressElabErrors_1015_ = lean_ctor_get_uint8(v___y_1008_, sizeof(void*)*3 + 1);
v_ref_1016_ = l_Lean_replaceRef(v_ref_1006_, v_ref_1013_);
lean_inc(v_currRecDepth_1012_);
lean_inc_ref(v_toCold_1011_);
v___x_1017_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1017_, 0, v_toCold_1011_);
lean_ctor_set(v___x_1017_, 1, v_currRecDepth_1012_);
lean_ctor_set(v___x_1017_, 2, v_ref_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*3, v_diag_1014_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*3 + 1, v_suppressElabErrors_1015_);
v___x_1018_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1007_, v___x_1017_, v___y_1009_);
lean_dec_ref_known(v___x_1017_, 3);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1019_, lean_object* v_msg_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1019_, v_msg_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v_ref_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1025_, lean_object* v_msg_1026_, lean_object* v_declHint_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v_a_1032_; lean_object* v___x_1033_; 
v___x_1031_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1026_, v_declHint_1027_, v___y_1028_, v___y_1029_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1025_, v_a_1032_, v___y_1028_, v___y_1029_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1034_, lean_object* v_msg_1035_, lean_object* v_declHint_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1034_, v_msg_1035_, v_declHint_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_ref_1034_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1047_, lean_object* v_constName_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1052_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1053_ = 0;
lean_inc(v_constName_1048_);
v___x_1054_ = l_Lean_MessageData_ofConstName(v_constName_1048_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1047_, v___x_1057_, v_constName_1048_, v___y_1049_, v___y_1050_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1059_, lean_object* v_constName_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1059_, v_constName_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_ref_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object* v_constName_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_ref_1069_; lean_object* v___x_1070_; 
v_ref_1069_ = lean_ctor_get(v___y_1066_, 2);
v___x_1070_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1069_, v_constName_1065_, v___y_1066_, v___y_1067_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object* v_constName_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v_env_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_st_ref_get(v___y_1078_);
v_env_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_ref(v_env_1081_);
lean_dec(v___x_1080_);
v___x_1082_ = 0;
lean_inc(v_constName_1076_);
v___x_1083_ = l_Lean_Environment_findConstVal_x3f(v_env_1081_, v_constName_1076_, v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1076_, v___y_1077_, v___y_1078_);
return v___x_1084_;
}
else
{
lean_object* v_val_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_constName_1076_);
v_val_1085_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_val_1085_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 0);
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_val_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object* v_constName_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__1(void){
_start:
{
lean_object* v___x_1104_; uint64_t v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__2(void){
_start:
{
uint64_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_uint64_once(&l_Lean_validateDefEqAttr___closed__1, &l_Lean_validateDefEqAttr___closed__1_once, _init_l_Lean_validateDefEqAttr___closed__1);
v___x_1107_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1108_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set_uint64(v___x_1108_, sizeof(void*)*1, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3(void){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__3, &l_Lean_validateDefEqAttr___closed__3_once, _init_l_Lean_validateDefEqAttr___closed__3);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = lean_box(1);
v___x_1113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1114_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1113_);
lean_ctor_set(v___x_1115_, 2, v___x_1112_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7(void){
_start:
{
uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1118_ = 1;
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_box(0);
v___x_1121_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__6));
v___x_1122_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__5, &l_Lean_validateDefEqAttr___closed__5_once, _init_l_Lean_validateDefEqAttr___closed__5);
v___x_1123_ = lean_box(1);
v___x_1124_ = 0;
v___x_1125_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__2, &l_Lean_validateDefEqAttr___closed__2_once, _init_l_Lean_validateDefEqAttr___closed__2);
v___x_1126_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1123_);
lean_ctor_set(v___x_1126_, 2, v___x_1122_);
lean_ctor_set(v___x_1126_, 3, v___x_1121_);
lean_ctor_set(v___x_1126_, 4, v___x_1120_);
lean_ctor_set(v___x_1126_, 5, v___x_1119_);
lean_ctor_set(v___x_1126_, 6, v___x_1120_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7 + 1, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7 + 2, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7 + 3, v___x_1118_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
lean_ctor_set(v___x_1129_, 2, v___x_1128_);
lean_ctor_set(v___x_1129_, 3, v___x_1128_);
lean_ctor_set(v___x_1129_, 4, v___x_1127_);
lean_ctor_set(v___x_1129_, 5, v___x_1127_);
lean_ctor_set(v___x_1129_, 6, v___x_1127_);
lean_ctor_set(v___x_1129_, 7, v___x_1127_);
lean_ctor_set(v___x_1129_, 8, v___x_1127_);
lean_ctor_set(v___x_1129_, 9, v___x_1127_);
lean_ctor_set(v___x_1129_, 10, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
lean_ctor_set(v___x_1131_, 2, v___x_1130_);
lean_ctor_set(v___x_1131_, 3, v___x_1130_);
lean_ctor_set(v___x_1131_, 4, v___x_1130_);
lean_ctor_set(v___x_1131_, 5, v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
lean_ctor_set(v___x_1133_, 3, v___x_1132_);
lean_ctor_set(v___x_1133_, 4, v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1134_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__10, &l_Lean_validateDefEqAttr___closed__10_once, _init_l_Lean_validateDefEqAttr___closed__10);
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1136_ = lean_box(1);
v___x_1137_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__9, &l_Lean_validateDefEqAttr___closed__9_once, _init_l_Lean_validateDefEqAttr___closed__9);
v___x_1138_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__8, &l_Lean_validateDefEqAttr___closed__8_once, _init_l_Lean_validateDefEqAttr___closed__8);
v___x_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___x_1137_);
lean_ctor_set(v___x_1139_, 2, v___x_1136_);
lean_ctor_set(v___x_1139_, 3, v___x_1135_);
lean_ctor_set(v___x_1139_, 4, v___x_1134_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object* v_declName_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_declName_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_type_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__7, &l_Lean_validateDefEqAttr___closed__7_once, _init_l_Lean_validateDefEqAttr___closed__7);
v___x_1148_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__11, &l_Lean_validateDefEqAttr___closed__11_once, _init_l_Lean_validateDefEqAttr___closed__11);
v___x_1149_ = lean_st_mk_ref(v___x_1148_);
v_type_1150_ = lean_ctor_get(v_a_1146_, 2);
lean_inc_ref(v_type_1150_);
lean_dec(v_a_1146_);
v___f_1151_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__12));
v___x_1152_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_1150_, v___f_1151_, v___x_1147_, v___x_1149_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_st_ref_get(v___x_1149_);
lean_dec(v___x_1149_);
lean_dec(v___x_1157_);
if (v_isShared_1156_ == 0)
{
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1153_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_dec(v___x_1149_);
return v___x_1152_;
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_a_1162_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1145_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1145_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object* v_declName_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_validateDefEqAttr(v_declName_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, uint8_t v_isExporting_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_1176_, v_isExporting_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_x_1185_, lean_object* v_isExporting_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_isExporting_boxed_1192_; lean_object* v_res_1193_; 
v_isExporting_boxed_1192_ = lean_unbox(v_isExporting_1186_);
v_res_1193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_1184_, v_x_1185_, v_isExporting_boxed_1192_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object* v_00_u03b1_1194_, lean_object* v_x_1195_, uint8_t v_when_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_1195_, v_when_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_x_1204_, lean_object* v_when_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_when_boxed_1211_; lean_object* v_res_1212_; 
v_when_boxed_1211_ = lean_unbox(v_when_1205_);
v_res_1212_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(v_00_u03b1_1203_, v_x_1204_, v_when_boxed_1211_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object* v_00_u03b1_1213_, lean_object* v_constName_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_constName_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_1219_, v_constName_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1225_, lean_object* v_ref_1226_, lean_object* v_constName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1226_, v_constName_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_ref_1233_, lean_object* v_constName_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_1232_, v_ref_1233_, v_constName_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v_ref_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1239_, lean_object* v_ref_1240_, lean_object* v_msg_1241_, lean_object* v_declHint_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1240_, v_msg_1241_, v_declHint_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_ref_1248_, lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1247_, v_ref_1248_, v_msg_1249_, v_declHint_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v_ref_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1255_, lean_object* v_declHint_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1255_, v_declHint_1256_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1261_, lean_object* v_declHint_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1261_, v_declHint_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1267_, lean_object* v_ref_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1268_, v_msg_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_ref_1275_, lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1274_, v_ref_1275_, v_msg_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v_ref_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1281_, lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_msg_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1287_, v_msg_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1306_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1307_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1308_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1309_ = 0;
v___x_1310_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1311_ = l_Lean_registerTagAttribute(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v___x_1309_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1(){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1317_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0));
v___x_1318_ = l_Lean_addBuiltinDocString(v___x_1316_, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1348_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6));
v___x_1349_ = l_Lean_addBuiltinDeclarationRanges(v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
return v_res_1351_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_1354_ = l_Lean_stringToMessageData(v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4));
v___x_1360_ = l_Lean_stringToMessageData(v___x_1359_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6));
v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_attrName_1364_, lean_object* v_declName_1365_, lean_object* v_asyncPrefix_x3f_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___y_1371_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1366_) == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_MessageData_nil;
v___y_1371_ = v___x_1384_;
goto v___jp_1370_;
}
else
{
lean_object* v_val_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_val_1385_ = lean_ctor_get(v_asyncPrefix_x3f_1366_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v_asyncPrefix_x3f_1366_, 1);
v___x_1386_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1387_ = l_Lean_MessageData_ofName(v_val_1385_);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___y_1371_ = v___x_1390_;
goto v___jp_1370_;
}
v___jp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1372_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1373_ = l_Lean_MessageData_ofName(v_attrName_1364_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = 0;
v___x_1378_ = l_Lean_MessageData_ofConstName(v_declName_1365_, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___y_1371_);
v___x_1383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1382_, v___y_1367_, v___y_1368_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1391_, lean_object* v_declName_1392_, lean_object* v_asyncPrefix_x3f_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1391_, v_declName_1392_, v_asyncPrefix_x3f_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1397_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_attrName_1401_, lean_object* v_declName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1406_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1407_ = l_Lean_MessageData_ofName(v_attrName_1401_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_MessageData_ofConstName(v_declName_1402_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1410_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1415_, v___y_1403_, v___y_1404_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1417_, lean_object* v_declName_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1417_, v_declName_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object* v_attr_1423_, lean_object* v_decl_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___y_1429_; lean_object* v___x_1455_; lean_object* v_env_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___x_1469_; 
v___x_1455_ = lean_st_ref_get(v___y_1426_);
v_env_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_ref(v_env_1456_);
lean_dec(v___x_1455_);
v___x_1469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1456_, v_decl_1424_);
if (lean_obj_tag(v___x_1469_) == 0)
{
v___y_1458_ = v___y_1425_;
v___y_1459_ = v___y_1426_;
goto v___jp_1457_;
}
else
{
lean_object* v_attr_1470_; lean_object* v_toAttributeImplCore_1471_; lean_object* v_name_1472_; lean_object* v___x_1473_; 
lean_dec_ref_known(v___x_1469_, 1);
lean_dec_ref(v_env_1456_);
v_attr_1470_ = lean_ctor_get(v_attr_1423_, 0);
lean_inc_ref(v_attr_1470_);
lean_dec_ref(v_attr_1423_);
v_toAttributeImplCore_1471_ = lean_ctor_get(v_attr_1470_, 0);
lean_inc_ref(v_toAttributeImplCore_1471_);
lean_dec_ref(v_attr_1470_);
v_name_1472_ = lean_ctor_get(v_toAttributeImplCore_1471_, 1);
lean_inc(v_name_1472_);
lean_dec_ref(v_toAttributeImplCore_1471_);
v___x_1473_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_1472_, v_decl_1424_, v___y_1425_, v___y_1426_);
return v___x_1473_;
}
v___jp_1428_:
{
lean_object* v___x_1430_; lean_object* v_ext_1431_; lean_object* v_toEnvExtension_1432_; lean_object* v_env_1433_; lean_object* v_nextMacroScope_1434_; lean_object* v_ngen_1435_; lean_object* v_auxDeclNGen_1436_; lean_object* v_traceState_1437_; lean_object* v_messages_1438_; lean_object* v_infoState_1439_; lean_object* v_snapshotTasks_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1453_; 
v___x_1430_ = lean_st_ref_take(v___y_1429_);
v_ext_1431_ = lean_ctor_get(v_attr_1423_, 1);
lean_inc_ref(v_ext_1431_);
lean_dec_ref(v_attr_1423_);
v_toEnvExtension_1432_ = lean_ctor_get(v_ext_1431_, 0);
v_env_1433_ = lean_ctor_get(v___x_1430_, 0);
v_nextMacroScope_1434_ = lean_ctor_get(v___x_1430_, 1);
v_ngen_1435_ = lean_ctor_get(v___x_1430_, 2);
v_auxDeclNGen_1436_ = lean_ctor_get(v___x_1430_, 3);
v_traceState_1437_ = lean_ctor_get(v___x_1430_, 4);
v_messages_1438_ = lean_ctor_get(v___x_1430_, 6);
v_infoState_1439_ = lean_ctor_get(v___x_1430_, 7);
v_snapshotTasks_1440_ = lean_ctor_get(v___x_1430_, 8);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1430_, 5);
lean_dec(v_unused_1454_);
v___x_1442_ = v___x_1430_;
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snapshotTasks_1440_);
lean_inc(v_infoState_1439_);
lean_inc(v_messages_1438_);
lean_inc(v_traceState_1437_);
lean_inc(v_auxDeclNGen_1436_);
lean_inc(v_ngen_1435_);
lean_inc(v_nextMacroScope_1434_);
lean_inc(v_env_1433_);
lean_dec(v___x_1430_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_asyncMode_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v_asyncMode_1444_ = lean_ctor_get(v_toEnvExtension_1432_, 2);
lean_inc(v_asyncMode_1444_);
lean_inc(v_decl_1424_);
v___x_1445_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1431_, v_env_1433_, v_decl_1424_, v_asyncMode_1444_, v_decl_1424_);
lean_dec(v_asyncMode_1444_);
v___x_1446_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 5, v___x_1446_);
lean_ctor_set(v___x_1442_, 0, v___x_1445_);
v___x_1448_ = v___x_1442_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_nextMacroScope_1434_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_ngen_1435_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_auxDeclNGen_1436_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_traceState_1437_);
lean_ctor_set(v_reuseFailAlloc_1452_, 5, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 6, v_messages_1438_);
lean_ctor_set(v_reuseFailAlloc_1452_, 7, v_infoState_1439_);
lean_ctor_set(v_reuseFailAlloc_1452_, 8, v_snapshotTasks_1440_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_st_ref_put(v___y_1429_, v___x_1448_);
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
v___jp_1457_:
{
lean_object* v_ext_1460_; lean_object* v_toEnvExtension_1461_; lean_object* v_attr_1462_; lean_object* v_asyncMode_1463_; uint8_t v___x_1464_; 
v_ext_1460_ = lean_ctor_get(v_attr_1423_, 1);
v_toEnvExtension_1461_ = lean_ctor_get(v_ext_1460_, 0);
v_attr_1462_ = lean_ctor_get(v_attr_1423_, 0);
v_asyncMode_1463_ = lean_ctor_get(v_toEnvExtension_1461_, 2);
lean_inc(v_decl_1424_);
lean_inc_ref(v_env_1456_);
v___x_1464_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1456_, v_decl_1424_, v_asyncMode_1463_);
if (v___x_1464_ == 0)
{
lean_object* v_toAttributeImplCore_1465_; lean_object* v_name_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v_attr_1462_);
lean_dec_ref(v_attr_1423_);
v_toAttributeImplCore_1465_ = lean_ctor_get(v_attr_1462_, 0);
lean_inc_ref(v_toAttributeImplCore_1465_);
lean_dec_ref(v_attr_1462_);
v_name_1466_ = lean_ctor_get(v_toAttributeImplCore_1465_, 1);
lean_inc(v_name_1466_);
lean_dec_ref(v_toAttributeImplCore_1465_);
v___x_1467_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1456_);
v___x_1468_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_1466_, v_decl_1424_, v___x_1467_, v___y_1458_, v___y_1459_);
return v___x_1468_;
}
else
{
lean_dec_ref(v_env_1456_);
v___y_1429_ = v___y_1459_;
goto v___jp_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object* v_attr_1474_, lean_object* v_decl_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1474_, v_decl_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object* v_declName_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
lean_inc(v_declName_1480_);
v___x_1484_ = l_Lean_validateDefEqAttr(v_declName_1480_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref_known(v___x_1484_, 1);
v___x_1485_ = l_Lean_backwardDefeqAttr;
v___x_1486_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v___x_1485_, v_declName_1480_, v___y_1481_, v___y_1482_);
return v___x_1486_;
}
else
{
lean_dec(v_declName_1480_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_declName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___f_1502_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1503_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1504_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1505_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1506_ = 0;
v___x_1507_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1508_ = l_Lean_registerTagAttribute(v___x_1503_, v___x_1504_, v___f_1502_, v___x_1505_, v___x_1506_, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1511_, lean_object* v_attrName_1512_, lean_object* v_declName_1513_, lean_object* v_asyncPrefix_x3f_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1512_, v_declName_1513_, v_asyncPrefix_x3f_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_attrName_1520_, lean_object* v_declName_1521_, lean_object* v_asyncPrefix_x3f_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1519_, v_attrName_1520_, v_declName_1521_, v_asyncPrefix_x3f_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_1527_, lean_object* v_attrName_1528_, lean_object* v_declName_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1528_, v_declName_1529_, v___y_1530_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_attrName_1535_, lean_object* v_declName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_1534_, v_attrName_1535_, v_declName_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1544_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0));
v___x_1545_ = l_Lean_addBuiltinDocString(v___x_1543_, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1575_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6));
v___x_1576_ = l_Lean_addBuiltinDeclarationRanges(v___x_1574_, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* v_type_1590_, lean_object* v_proof_1591_, lean_object* v_a_1592_){
_start:
{
if (lean_obj_tag(v_type_1590_) == 7)
{
if (lean_obj_tag(v_proof_1591_) == 6)
{
lean_object* v_body_1594_; lean_object* v_body_1595_; 
v_body_1594_ = lean_ctor_get(v_type_1590_, 2);
v_body_1595_ = lean_ctor_get(v_proof_1591_, 2);
lean_inc_ref(v_body_1595_);
lean_dec_ref_known(v_proof_1591_, 3);
v_type_1590_ = v_body_1594_;
v_proof_1591_ = v_body_1595_;
goto _start;
}
else
{
uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v_proof_1591_);
v___x_1597_ = 0;
v___x_1598_ = lean_box(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_1601_ = lean_unsigned_to_nat(3u);
v___x_1602_ = l_Lean_Expr_isAppOfArity(v_type_1590_, v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v_proof_1591_);
v___x_1603_ = lean_box(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1));
v___x_1606_ = lean_unsigned_to_nat(2u);
v___x_1607_ = l_Lean_Expr_isAppOfArity(v_proof_1591_, v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3));
v___x_1609_ = l_Lean_Expr_isAppOfArity(v_proof_1591_, v___x_1608_, v___x_1606_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5));
v___x_1611_ = lean_unsigned_to_nat(4u);
v___x_1612_ = l_Lean_Expr_isAppOfArity(v_proof_1591_, v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = l_Lean_Expr_getAppFn(v_proof_1591_);
lean_dec_ref(v_proof_1591_);
v___x_1614_ = l_Lean_Expr_isConst(v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v___x_1613_);
v___x_1615_ = lean_box(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v_env_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1617_ = lean_st_ref_get(v_a_1592_);
v_env_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref_n(v_env_1618_, 2);
lean_dec(v___x_1617_);
v___x_1619_ = l_Lean_Expr_constName_x21(v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1620_ = l_Lean_defeqAttr;
lean_inc(v___x_1619_);
v___x_1621_ = l_Lean_TagAttribute_hasTag(v___x_1620_, v_env_1618_, v___x_1619_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = l_Lean_backwardDefeqAttr;
v___x_1623_ = l_Lean_TagAttribute_hasTag(v___x_1622_, v_env_1618_, v___x_1619_);
v___x_1624_ = lean_box(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v___x_1619_);
lean_dec_ref(v_env_1618_);
v___x_1626_ = lean_box(v___x_1602_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Expr_appArg_x21(v_proof_1591_);
lean_dec_ref(v_proof_1591_);
v_proof_1591_ = v___x_1628_;
goto _start;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref(v_proof_1591_);
v___x_1630_ = lean_box(v___x_1602_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_proof_1591_);
v___x_1632_ = lean_box(v___x_1602_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* v_type_1634_, lean_object* v_proof_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1634_, v_proof_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_type_1634_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* v_type_1639_, lean_object* v_proof_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1639_, v_proof_1640_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* v_type_1645_, lean_object* v_proof_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1645_, v_proof_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec_ref(v_type_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object* v_attrName_1651_, lean_object* v_declName_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1658_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1659_ = l_Lean_MessageData_ofName(v_attrName_1651_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = 0;
v___x_1664_ = l_Lean_MessageData_ofConstName(v_declName_1652_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1662_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1667_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1669_, lean_object* v_declName_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1669_, v_declName_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object* v_attrName_1677_, lean_object* v_declName_1678_, lean_object* v_asyncPrefix_x3f_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___y_1686_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1679_) == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_MessageData_nil;
v___y_1686_ = v___x_1699_;
goto v___jp_1685_;
}
else
{
lean_object* v_val_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_val_1700_ = lean_ctor_get(v_asyncPrefix_x3f_1679_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v_asyncPrefix_x3f_1679_, 1);
v___x_1701_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1702_ = l_Lean_MessageData_ofName(v_val_1700_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___y_1686_ = v___x_1705_;
goto v___jp_1685_;
}
v___jp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1687_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1688_ = l_Lean_MessageData_ofName(v_attrName_1677_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = 0;
v___x_1693_ = l_Lean_MessageData_ofConstName(v_declName_1678_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1691_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___y_1686_);
v___x_1698_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1697_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1706_, lean_object* v_declName_1707_, lean_object* v_asyncPrefix_x3f_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1706_, v_declName_1707_, v_asyncPrefix_x3f_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object* v_attr_1715_, lean_object* v_decl_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___x_1765_; lean_object* v_env_1766_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___x_1781_; 
v___x_1765_ = lean_st_ref_get(v___y_1720_);
v_env_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_ref(v_env_1766_);
lean_dec(v___x_1765_);
v___x_1781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1766_, v_decl_1716_);
if (lean_obj_tag(v___x_1781_) == 0)
{
v___y_1768_ = v___y_1717_;
v___y_1769_ = v___y_1718_;
v___y_1770_ = v___y_1719_;
v___y_1771_ = v___y_1720_;
goto v___jp_1767_;
}
else
{
lean_object* v_attr_1782_; lean_object* v_toAttributeImplCore_1783_; lean_object* v_name_1784_; lean_object* v___x_1785_; 
lean_dec_ref_known(v___x_1781_, 1);
lean_dec_ref(v_env_1766_);
v_attr_1782_ = lean_ctor_get(v_attr_1715_, 0);
lean_inc_ref(v_attr_1782_);
lean_dec_ref(v_attr_1715_);
v_toAttributeImplCore_1783_ = lean_ctor_get(v_attr_1782_, 0);
lean_inc_ref(v_toAttributeImplCore_1783_);
lean_dec_ref(v_attr_1782_);
v_name_1784_ = lean_ctor_get(v_toAttributeImplCore_1783_, 1);
lean_inc(v_name_1784_);
lean_dec_ref(v_toAttributeImplCore_1783_);
v___x_1785_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_1784_, v_decl_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1785_;
}
v___jp_1722_:
{
lean_object* v___x_1725_; lean_object* v_ext_1726_; lean_object* v_toEnvExtension_1727_; lean_object* v_env_1728_; lean_object* v_nextMacroScope_1729_; lean_object* v_ngen_1730_; lean_object* v_auxDeclNGen_1731_; lean_object* v_traceState_1732_; lean_object* v_messages_1733_; lean_object* v_infoState_1734_; lean_object* v_snapshotTasks_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1763_; 
v___x_1725_ = lean_st_ref_take(v___y_1724_);
v_ext_1726_ = lean_ctor_get(v_attr_1715_, 1);
lean_inc_ref(v_ext_1726_);
lean_dec_ref(v_attr_1715_);
v_toEnvExtension_1727_ = lean_ctor_get(v_ext_1726_, 0);
v_env_1728_ = lean_ctor_get(v___x_1725_, 0);
v_nextMacroScope_1729_ = lean_ctor_get(v___x_1725_, 1);
v_ngen_1730_ = lean_ctor_get(v___x_1725_, 2);
v_auxDeclNGen_1731_ = lean_ctor_get(v___x_1725_, 3);
v_traceState_1732_ = lean_ctor_get(v___x_1725_, 4);
v_messages_1733_ = lean_ctor_get(v___x_1725_, 6);
v_infoState_1734_ = lean_ctor_get(v___x_1725_, 7);
v_snapshotTasks_1735_ = lean_ctor_get(v___x_1725_, 8);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1725_, 5);
lean_dec(v_unused_1764_);
v___x_1737_ = v___x_1725_;
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snapshotTasks_1735_);
lean_inc(v_infoState_1734_);
lean_inc(v_messages_1733_);
lean_inc(v_traceState_1732_);
lean_inc(v_auxDeclNGen_1731_);
lean_inc(v_ngen_1730_);
lean_inc(v_nextMacroScope_1729_);
lean_inc(v_env_1728_);
lean_dec(v___x_1725_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_asyncMode_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v_asyncMode_1739_ = lean_ctor_get(v_toEnvExtension_1727_, 2);
lean_inc(v_asyncMode_1739_);
lean_inc(v_decl_1716_);
v___x_1740_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1726_, v_env_1728_, v_decl_1716_, v_asyncMode_1739_, v_decl_1716_);
lean_dec(v_asyncMode_1739_);
v___x_1741_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 5, v___x_1741_);
lean_ctor_set(v___x_1737_, 0, v___x_1740_);
v___x_1743_ = v___x_1737_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1729_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1730_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_traceState_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1733_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1734_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1735_);
v___x_1743_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_mctx_1746_; lean_object* v_zetaDeltaFVarIds_1747_; lean_object* v_postponed_1748_; lean_object* v_diag_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1760_; 
v___x_1744_ = lean_st_ref_put(v___y_1724_, v___x_1743_);
v___x_1745_ = lean_st_ref_take(v___y_1723_);
v_mctx_1746_ = lean_ctor_get(v___x_1745_, 0);
v_zetaDeltaFVarIds_1747_ = lean_ctor_get(v___x_1745_, 2);
v_postponed_1748_ = lean_ctor_get(v___x_1745_, 3);
v_diag_1749_ = lean_ctor_get(v___x_1745_, 4);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1745_, 1);
lean_dec(v_unused_1761_);
v___x_1751_ = v___x_1745_;
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_diag_1749_);
lean_inc(v_postponed_1748_);
lean_inc(v_zetaDeltaFVarIds_1747_);
lean_inc(v_mctx_1746_);
lean_dec(v___x_1745_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_mctx_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_zetaDeltaFVarIds_1747_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_postponed_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_diag_1749_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_st_ref_put(v___y_1723_, v___x_1755_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
}
}
v___jp_1767_:
{
lean_object* v_ext_1772_; lean_object* v_toEnvExtension_1773_; lean_object* v_attr_1774_; lean_object* v_asyncMode_1775_; uint8_t v___x_1776_; 
v_ext_1772_ = lean_ctor_get(v_attr_1715_, 1);
v_toEnvExtension_1773_ = lean_ctor_get(v_ext_1772_, 0);
v_attr_1774_ = lean_ctor_get(v_attr_1715_, 0);
v_asyncMode_1775_ = lean_ctor_get(v_toEnvExtension_1773_, 2);
lean_inc(v_decl_1716_);
lean_inc_ref(v_env_1766_);
v___x_1776_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1766_, v_decl_1716_, v_asyncMode_1775_);
if (v___x_1776_ == 0)
{
lean_object* v_toAttributeImplCore_1777_; lean_object* v_name_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_inc_ref(v_attr_1774_);
lean_dec_ref(v_attr_1715_);
v_toAttributeImplCore_1777_ = lean_ctor_get(v_attr_1774_, 0);
lean_inc_ref(v_toAttributeImplCore_1777_);
lean_dec_ref(v_attr_1774_);
v_name_1778_ = lean_ctor_get(v_toAttributeImplCore_1777_, 1);
lean_inc(v_name_1778_);
lean_dec_ref(v_toAttributeImplCore_1777_);
v___x_1779_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1766_);
v___x_1780_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_1778_, v_decl_1716_, v___x_1779_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1780_;
}
else
{
lean_dec_ref(v_env_1766_);
v___y_1723_ = v___y_1769_;
v___y_1724_ = v___y_1771_;
goto v___jp_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object* v_attr_1786_, lean_object* v_decl_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_1786_, v_decl_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1794_, lean_object* v_declHint_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_st_ref_get(v___y_1796_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_ref(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1800_ = l_Lean_Name_isAnonymous(v_declHint_1795_);
if (v___x_1800_ == 0)
{
uint8_t v_isExporting_1801_; 
v_isExporting_1801_ = lean_ctor_get_uint8(v_env_1799_, sizeof(void*)*8);
if (v_isExporting_1801_ == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_msg_1794_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
lean_inc_ref(v_env_1799_);
v___x_1803_ = l_Lean_Environment_setExporting(v_env_1799_, v___x_1800_);
lean_inc(v_declHint_1795_);
lean_inc_ref(v___x_1803_);
v___x_1804_ = l_Lean_Environment_contains(v___x_1803_, v_declHint_1795_, v_isExporting_1801_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_msg_1794_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_c_1813_; lean_object* v___x_1814_; 
v___x_1806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1807_ = lean_unsigned_to_nat(32u);
v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
lean_dec_ref(v___x_1808_);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1810_ = l_Lean_Options_empty;
v___x_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1803_);
lean_ctor_set(v___x_1811_, 1, v___x_1806_);
lean_ctor_set(v___x_1811_, 2, v___x_1809_);
lean_ctor_set(v___x_1811_, 3, v___x_1810_);
lean_inc(v_declHint_1795_);
v___x_1812_ = l_Lean_MessageData_ofConstName(v_declHint_1795_, v___x_1800_);
v_c_1813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1813_, 0, v___x_1811_);
lean_ctor_set(v_c_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1799_, v_declHint_1795_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_c_1813_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_MessageData_note(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_msg_1794_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1857_; 
v_val_1822_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1824_ = v___x_1814_;
v_isShared_1825_ = v_isSharedCheck_1857_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v___x_1814_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1857_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_mod_1829_; uint8_t v___x_1830_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_Environment_header(v_env_1799_);
lean_dec_ref(v_env_1799_);
v___x_1828_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1827_);
v_mod_1829_ = lean_array_get(v___x_1826_, v___x_1828_, v_val_1822_);
lean_dec(v_val_1822_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = l_Lean_isPrivateName(v_declHint_1795_);
lean_dec(v_declHint_1795_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v_c_1813_);
v___x_1833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_MessageData_ofName(v_mod_1829_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_MessageData_note(v___x_1838_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_msg_1794_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1840_);
v___x_1842_ = v___x_1824_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v_c_1813_);
v___x_1846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_MessageData_ofName(v_mod_1829_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_MessageData_note(v___x_1851_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_msg_1794_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1853_);
v___x_1855_ = v___x_1824_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref(v_env_1799_);
lean_dec(v_declHint_1795_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_msg_1794_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1859_, lean_object* v_declHint_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1859_, v_declHint_1860_, v___y_1861_);
lean_dec(v___y_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object* v_msg_1864_, lean_object* v_declHint_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1881_; 
v___x_1871_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1864_, v_declHint_1865_, v___y_1869_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1876_ = l_Lean_unknownIdentifierMessageTag;
v___x_1877_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object* v_msg_1882_, lean_object* v_declHint_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1882_, v_declHint_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object* v_ref_1890_, lean_object* v_msg_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_toCold_1897_; lean_object* v_currRecDepth_1898_; lean_object* v_ref_1899_; uint8_t v_diag_1900_; uint8_t v_suppressElabErrors_1901_; lean_object* v_ref_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_toCold_1897_ = lean_ctor_get(v___y_1894_, 0);
v_currRecDepth_1898_ = lean_ctor_get(v___y_1894_, 1);
v_ref_1899_ = lean_ctor_get(v___y_1894_, 2);
v_diag_1900_ = lean_ctor_get_uint8(v___y_1894_, sizeof(void*)*3);
v_suppressElabErrors_1901_ = lean_ctor_get_uint8(v___y_1894_, sizeof(void*)*3 + 1);
v_ref_1902_ = l_Lean_replaceRef(v_ref_1890_, v_ref_1899_);
lean_inc(v_currRecDepth_1898_);
lean_inc_ref(v_toCold_1897_);
v___x_1903_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1903_, 0, v_toCold_1897_);
lean_ctor_set(v___x_1903_, 1, v_currRecDepth_1898_);
lean_ctor_set(v___x_1903_, 2, v_ref_1902_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*3, v_diag_1900_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*3 + 1, v_suppressElabErrors_1901_);
v___x_1904_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_1891_, v___y_1892_, v___y_1893_, v___x_1903_, v___y_1895_);
lean_dec_ref_known(v___x_1903_, 3);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1905_, v_msg_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_ref_1905_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object* v_ref_1913_, lean_object* v_msg_1914_, lean_object* v_declHint_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; 
v___x_1921_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1914_, v_declHint_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1913_, v_a_1922_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1924_, lean_object* v_msg_1925_, lean_object* v_declHint_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1924_, v_msg_1925_, v_declHint_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_ref_1924_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object* v_ref_1933_, lean_object* v_constName_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1940_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1941_ = 0;
lean_inc(v_constName_1934_);
v___x_1942_ = l_Lean_MessageData_ofConstName(v_constName_1934_, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1940_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1933_, v___x_1945_, v_constName_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object* v_ref_1947_, lean_object* v_constName_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1947_, v_constName_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_ref_1947_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object* v_constName_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_ref_1961_; lean_object* v___x_1962_; 
v_ref_1961_ = lean_ctor_get(v___y_1958_, 2);
v___x_1962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1961_, v_constName_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object* v_constName_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object* v_constName_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v_env_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = lean_st_ref_get(v___y_1974_);
v_env_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_ref(v_env_1977_);
lean_dec(v___x_1976_);
v___x_1978_ = 0;
lean_inc(v_constName_1970_);
v___x_1979_ = l_Lean_Environment_find_x3f(v_env_1977_, v_constName_1970_, v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1980_;
}
else
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_constName_1970_);
v_val_1981_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 0);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_val_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object* v_constName_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v_res_1995_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_2003_, uint8_t v___y_2004_, lean_object* v_x_2005_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 1)
{
lean_object* v_pre_2006_; 
v_pre_2006_ = lean_ctor_get(v_x_2005_, 0);
switch(lean_obj_tag(v_pre_2006_))
{
case 1:
{
lean_object* v_pre_2007_; 
v_pre_2007_ = lean_ctor_get(v_pre_2006_, 0);
switch(lean_obj_tag(v_pre_2007_))
{
case 0:
{
lean_object* v_str_2008_; lean_object* v_str_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_str_2008_ = lean_ctor_get(v_x_2005_, 1);
v_str_2009_ = lean_ctor_get(v_pre_2006_, 1);
v___x_2010_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0));
v___x_2011_ = lean_string_dec_eq(v_str_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1));
v___x_2013_ = lean_string_dec_eq(v_str_2009_, v___x_2012_);
if (v___x_2013_ == 0)
{
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2));
v___x_2015_ = lean_string_dec_eq(v_str_2008_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3));
v___x_2017_ = lean_string_dec_eq(v_str_2008_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v___x_2017_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
case 1:
{
lean_object* v_pre_2018_; 
v_pre_2018_ = lean_ctor_get(v_pre_2007_, 0);
if (lean_obj_tag(v_pre_2018_) == 0)
{
lean_object* v_str_2019_; lean_object* v_str_2020_; lean_object* v_str_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_str_2019_ = lean_ctor_get(v_x_2005_, 1);
v_str_2020_ = lean_ctor_get(v_pre_2006_, 1);
v_str_2021_ = lean_ctor_get(v_pre_2007_, 1);
v___x_2022_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4));
v___x_2023_ = lean_string_dec_eq(v_str_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5));
v___x_2025_ = lean_string_dec_eq(v_str_2020_, v___x_2024_);
if (v___x_2025_ == 0)
{
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6));
v___x_2027_ = lean_string_dec_eq(v_str_2019_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___x_2027_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
}
else
{
return v___y_2004_;
}
}
default: 
{
return v___y_2004_;
}
}
}
case 0:
{
lean_object* v_str_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_str_2028_ = lean_ctor_get(v_x_2005_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0));
v___x_2030_ = lean_string_dec_eq(v_str_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
return v___x_2030_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
default: 
{
return v___y_2004_;
}
}
}
else
{
return v___y_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_2031_, lean_object* v___y_2032_, lean_object* v_x_2033_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2034_; uint8_t v___y_8330__boxed_2035_; uint8_t v_res_2036_; lean_object* v_r_2037_; 
v_suppressElabErrors_boxed_2034_ = lean_unbox(v_suppressElabErrors_2031_);
v___y_8330__boxed_2035_ = lean_unbox(v___y_2032_);
v_res_2036_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_2034_, v___y_8330__boxed_2035_, v_x_2033_);
lean_dec(v_x_2033_);
v_r_2037_ = lean_box(v_res_2036_);
return v_r_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object* v_ref_2039_, lean_object* v_msgData_2040_, uint8_t v_severity_2041_, uint8_t v_isSilent_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; uint8_t v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2122_; uint8_t v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; uint8_t v___y_2128_; uint8_t v___x_2133_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; uint8_t v___y_2139_; lean_object* v___y_2140_; uint8_t v___y_2141_; uint8_t v___y_2143_; uint8_t v___x_2159_; 
v___x_2133_ = 2;
v___x_2159_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2041_, v___x_2133_);
if (v___x_2159_ == 0)
{
v___y_2143_ = v___x_2159_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2160_; 
lean_inc_ref(v_msgData_2040_);
v___x_2160_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2040_);
v___y_2143_ = v___x_2160_;
goto v___jp_2142_;
}
v___jp_2048_:
{
lean_object* v___x_2058_; lean_object* v_toCold_2059_; lean_object* v_currNamespace_2060_; lean_object* v_openDecls_2061_; lean_object* v_env_2062_; lean_object* v_nextMacroScope_2063_; lean_object* v_ngen_2064_; lean_object* v_auxDeclNGen_2065_; lean_object* v_traceState_2066_; lean_object* v_cache_2067_; lean_object* v_messages_2068_; lean_object* v_infoState_2069_; lean_object* v_snapshotTasks_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2084_; 
v___x_2058_ = lean_st_ref_take(v___y_2057_);
v_toCold_2059_ = lean_ctor_get(v___y_2056_, 0);
v_currNamespace_2060_ = lean_ctor_get(v_toCold_2059_, 4);
v_openDecls_2061_ = lean_ctor_get(v_toCold_2059_, 5);
v_env_2062_ = lean_ctor_get(v___x_2058_, 0);
v_nextMacroScope_2063_ = lean_ctor_get(v___x_2058_, 1);
v_ngen_2064_ = lean_ctor_get(v___x_2058_, 2);
v_auxDeclNGen_2065_ = lean_ctor_get(v___x_2058_, 3);
v_traceState_2066_ = lean_ctor_get(v___x_2058_, 4);
v_cache_2067_ = lean_ctor_get(v___x_2058_, 5);
v_messages_2068_ = lean_ctor_get(v___x_2058_, 6);
v_infoState_2069_ = lean_ctor_get(v___x_2058_, 7);
v_snapshotTasks_2070_ = lean_ctor_get(v___x_2058_, 8);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2072_ = v___x_2058_;
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snapshotTasks_2070_);
lean_inc(v_infoState_2069_);
lean_inc(v_messages_2068_);
lean_inc(v_cache_2067_);
lean_inc(v_traceState_2066_);
lean_inc(v_auxDeclNGen_2065_);
lean_inc(v_ngen_2064_);
lean_inc(v_nextMacroScope_2063_);
lean_inc(v_env_2062_);
lean_dec(v___x_2058_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
lean_inc(v_openDecls_2061_);
lean_inc(v_currNamespace_2060_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_currNamespace_2060_);
lean_ctor_set(v___x_2074_, 1, v_openDecls_2061_);
v___x_2075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___y_2050_);
lean_inc_ref(v___y_2053_);
lean_inc_ref(v___y_2055_);
v___x_2076_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2076_, 0, v___y_2055_);
lean_ctor_set(v___x_2076_, 1, v___y_2051_);
lean_ctor_set(v___x_2076_, 2, v___y_2052_);
lean_ctor_set(v___x_2076_, 3, v___y_2053_);
lean_ctor_set(v___x_2076_, 4, v___x_2075_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*5, v___y_2049_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*5 + 1, v___y_2054_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*5 + 2, v_isSilent_2042_);
v___x_2077_ = l_Lean_MessageLog_add(v___x_2076_, v_messages_2068_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 6, v___x_2077_);
v___x_2079_ = v___x_2072_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_env_2062_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_nextMacroScope_2063_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_ngen_2064_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_auxDeclNGen_2065_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_traceState_2066_);
lean_ctor_set(v_reuseFailAlloc_2083_, 5, v_cache_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 6, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2083_, 7, v_infoState_2069_);
lean_ctor_set(v_reuseFailAlloc_2083_, 8, v_snapshotTasks_2070_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_st_ref_put(v___y_2057_, v___x_2079_);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
}
v___jp_2085_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2109_; 
v___x_2094_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2040_);
v___x_2095_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_2094_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_inc_ref_n(v___y_2092_, 2);
v___x_2100_ = l_Lean_FileMap_toPosition(v___y_2092_, v___y_2091_);
lean_dec(v___y_2091_);
v___x_2101_ = l_Lean_FileMap_toPosition(v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0));
if (v___y_2087_ == 0)
{
lean_del_object(v___x_2098_);
lean_dec_ref(v___y_2086_);
v___y_2049_ = v___y_2088_;
v___y_2050_ = v_a_2096_;
v___y_2051_ = v___x_2100_;
v___y_2052_ = v___x_2102_;
v___y_2053_ = v___x_2103_;
v___y_2054_ = v___y_2090_;
v___y_2055_ = v___y_2089_;
v___y_2056_ = v___y_2045_;
v___y_2057_ = v___y_2046_;
goto v___jp_2048_;
}
else
{
uint8_t v___x_2104_; 
lean_inc(v_a_2096_);
v___x_2104_ = l_Lean_MessageData_hasTag(v___y_2086_, v_a_2096_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec_ref_known(v___x_2102_, 1);
lean_dec_ref(v___x_2100_);
lean_dec(v_a_2096_);
v___x_2105_ = lean_box(0);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2105_);
v___x_2107_ = v___x_2098_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_del_object(v___x_2098_);
v___y_2049_ = v___y_2088_;
v___y_2050_ = v_a_2096_;
v___y_2051_ = v___x_2100_;
v___y_2052_ = v___x_2102_;
v___y_2053_ = v___x_2103_;
v___y_2054_ = v___y_2090_;
v___y_2055_ = v___y_2089_;
v___y_2056_ = v___y_2045_;
v___y_2057_ = v___y_2046_;
goto v___jp_2048_;
}
}
}
}
v___jp_2110_:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Syntax_getTailPos_x3f(v___y_2114_, v___y_2112_);
lean_dec(v___y_2114_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_inc(v___y_2118_);
v___y_2086_ = v___y_2111_;
v___y_2087_ = v___y_2113_;
v___y_2088_ = v___y_2112_;
v___y_2089_ = v___y_2116_;
v___y_2090_ = v___y_2115_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v___y_2117_;
v___y_2093_ = v___y_2118_;
goto v___jp_2085_;
}
else
{
lean_object* v_val_2120_; 
v_val_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___y_2086_ = v___y_2111_;
v___y_2087_ = v___y_2113_;
v___y_2088_ = v___y_2112_;
v___y_2089_ = v___y_2116_;
v___y_2090_ = v___y_2115_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v___y_2117_;
v___y_2093_ = v_val_2120_;
goto v___jp_2085_;
}
}
v___jp_2121_:
{
lean_object* v_ref_2129_; lean_object* v___x_2130_; 
v_ref_2129_ = l_Lean_replaceRef(v_ref_2039_, v___y_2125_);
v___x_2130_ = l_Lean_Syntax_getPos_x3f(v_ref_2129_, v___y_2124_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v___y_2111_ = v___y_2122_;
v___y_2112_ = v___y_2124_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v_ref_2129_;
v___y_2115_ = v___y_2128_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v___x_2131_;
goto v___jp_2110_;
}
else
{
lean_object* v_val_2132_; 
v_val_2132_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2111_ = v___y_2122_;
v___y_2112_ = v___y_2124_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v_ref_2129_;
v___y_2115_ = v___y_2128_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v_val_2132_;
goto v___jp_2110_;
}
}
v___jp_2134_:
{
if (v___y_2141_ == 0)
{
v___y_2122_ = v___y_2135_;
v___y_2123_ = v___y_2139_;
v___y_2124_ = v___y_2138_;
v___y_2125_ = v___y_2140_;
v___y_2126_ = v___y_2136_;
v___y_2127_ = v___y_2137_;
v___y_2128_ = v_severity_2041_;
goto v___jp_2121_;
}
else
{
v___y_2122_ = v___y_2135_;
v___y_2123_ = v___y_2139_;
v___y_2124_ = v___y_2138_;
v___y_2125_ = v___y_2140_;
v___y_2126_ = v___y_2136_;
v___y_2127_ = v___y_2137_;
v___y_2128_ = v___x_2133_;
goto v___jp_2121_;
}
}
v___jp_2142_:
{
if (v___y_2143_ == 0)
{
lean_object* v_toCold_2144_; lean_object* v_ref_2145_; uint8_t v_suppressElabErrors_2146_; lean_object* v_fileName_2147_; lean_object* v_fileMap_2148_; lean_object* v_options_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; uint8_t v___x_2153_; uint8_t v___x_2154_; 
v_toCold_2144_ = lean_ctor_get(v___y_2045_, 0);
v_ref_2145_ = lean_ctor_get(v___y_2045_, 2);
v_suppressElabErrors_2146_ = lean_ctor_get_uint8(v___y_2045_, sizeof(void*)*3 + 1);
v_fileName_2147_ = lean_ctor_get(v_toCold_2144_, 0);
v_fileMap_2148_ = lean_ctor_get(v_toCold_2144_, 1);
v_options_2149_ = lean_ctor_get(v_toCold_2144_, 2);
v___x_2150_ = lean_box(v_suppressElabErrors_2146_);
v___x_2151_ = lean_box(v___y_2143_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2152_, 0, v___x_2150_);
lean_closure_set(v___f_2152_, 1, v___x_2151_);
v___x_2153_ = 1;
v___x_2154_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2041_, v___x_2153_);
if (v___x_2154_ == 0)
{
v___y_2135_ = v___f_2152_;
v___y_2136_ = v_fileName_2147_;
v___y_2137_ = v_fileMap_2148_;
v___y_2138_ = v___y_2143_;
v___y_2139_ = v_suppressElabErrors_2146_;
v___y_2140_ = v_ref_2145_;
v___y_2141_ = v___x_2154_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = l_Lean_warningAsError;
v___x_2156_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_2149_, v___x_2155_);
v___y_2135_ = v___f_2152_;
v___y_2136_ = v_fileName_2147_;
v___y_2137_ = v_fileMap_2148_;
v___y_2138_ = v___y_2143_;
v___y_2139_ = v_suppressElabErrors_2146_;
v___y_2140_ = v_ref_2145_;
v___y_2141_ = v___x_2156_;
goto v___jp_2134_;
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v_msgData_2040_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object* v_ref_2161_, lean_object* v_msgData_2162_, lean_object* v_severity_2163_, lean_object* v_isSilent_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v_severity_boxed_2170_; uint8_t v_isSilent_boxed_2171_; lean_object* v_res_2172_; 
v_severity_boxed_2170_ = lean_unbox(v_severity_2163_);
v_isSilent_boxed_2171_ = lean_unbox(v_isSilent_2164_);
v_res_2172_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2161_, v_msgData_2162_, v_severity_boxed_2170_, v_isSilent_boxed_2171_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_ref_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object* v_msgData_2173_, uint8_t v_severity_2174_, uint8_t v_isSilent_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_ref_2181_; lean_object* v___x_2182_; 
v_ref_2181_ = lean_ctor_get(v___y_2178_, 2);
v___x_2182_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2181_, v_msgData_2173_, v_severity_2174_, v_isSilent_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object* v_msgData_2183_, lean_object* v_severity_2184_, lean_object* v_isSilent_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v_severity_boxed_2191_; uint8_t v_isSilent_boxed_2192_; lean_object* v_res_2193_; 
v_severity_boxed_2191_ = lean_unbox(v_severity_2184_);
v_isSilent_boxed_2192_ = lean_unbox(v_isSilent_2185_);
v_res_2193_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2183_, v_severity_boxed_2191_, v_isSilent_boxed_2192_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object* v_msgData_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = 2;
v___x_2201_ = 0;
v___x_2202_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2194_, v___x_2200_, v___x_2201_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object* v_msgData_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object* v___y_2210_, uint8_t v_isExporting_2211_, lean_object* v___x_2212_, lean_object* v___y_2213_, lean_object* v___x_2214_, lean_object* v_a_x3f_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v_env_2218_; lean_object* v_nextMacroScope_2219_; lean_object* v_ngen_2220_; lean_object* v_auxDeclNGen_2221_; lean_object* v_traceState_2222_; lean_object* v_messages_2223_; lean_object* v_infoState_2224_; lean_object* v_snapshotTasks_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2250_; 
v___x_2217_ = lean_st_ref_take(v___y_2210_);
v_env_2218_ = lean_ctor_get(v___x_2217_, 0);
v_nextMacroScope_2219_ = lean_ctor_get(v___x_2217_, 1);
v_ngen_2220_ = lean_ctor_get(v___x_2217_, 2);
v_auxDeclNGen_2221_ = lean_ctor_get(v___x_2217_, 3);
v_traceState_2222_ = lean_ctor_get(v___x_2217_, 4);
v_messages_2223_ = lean_ctor_get(v___x_2217_, 6);
v_infoState_2224_ = lean_ctor_get(v___x_2217_, 7);
v_snapshotTasks_2225_ = lean_ctor_get(v___x_2217_, 8);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2217_, 5);
lean_dec(v_unused_2251_);
v___x_2227_ = v___x_2217_;
v_isShared_2228_ = v_isSharedCheck_2250_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snapshotTasks_2225_);
lean_inc(v_infoState_2224_);
lean_inc(v_messages_2223_);
lean_inc(v_traceState_2222_);
lean_inc(v_auxDeclNGen_2221_);
lean_inc(v_ngen_2220_);
lean_inc(v_nextMacroScope_2219_);
lean_inc(v_env_2218_);
lean_dec(v___x_2217_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2250_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = l_Lean_Environment_setExporting(v_env_2218_, v_isExporting_2211_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 5, v___x_2212_);
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_nextMacroScope_2219_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_ngen_2220_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_auxDeclNGen_2221_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_traceState_2222_);
lean_ctor_set(v_reuseFailAlloc_2249_, 5, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2249_, 6, v_messages_2223_);
lean_ctor_set(v_reuseFailAlloc_2249_, 7, v_infoState_2224_);
lean_ctor_set(v_reuseFailAlloc_2249_, 8, v_snapshotTasks_2225_);
v___x_2231_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_mctx_2234_; lean_object* v_zetaDeltaFVarIds_2235_; lean_object* v_postponed_2236_; lean_object* v_diag_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2247_; 
v___x_2232_ = lean_st_ref_put(v___y_2210_, v___x_2231_);
v___x_2233_ = lean_st_ref_take(v___y_2213_);
v_mctx_2234_ = lean_ctor_get(v___x_2233_, 0);
v_zetaDeltaFVarIds_2235_ = lean_ctor_get(v___x_2233_, 2);
v_postponed_2236_ = lean_ctor_get(v___x_2233_, 3);
v_diag_2237_ = lean_ctor_get(v___x_2233_, 4);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2233_, 1);
lean_dec(v_unused_2248_);
v___x_2239_ = v___x_2233_;
v_isShared_2240_ = v_isSharedCheck_2247_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_diag_2237_);
lean_inc(v_postponed_2236_);
lean_inc(v_zetaDeltaFVarIds_2235_);
lean_inc(v_mctx_2234_);
lean_dec(v___x_2233_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2247_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v___x_2214_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_mctx_2234_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_zetaDeltaFVarIds_2235_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_postponed_2236_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_diag_2237_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_st_ref_put(v___y_2213_, v___x_2242_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object* v___y_2252_, lean_object* v_isExporting_2253_, lean_object* v___x_2254_, lean_object* v___y_2255_, lean_object* v___x_2256_, lean_object* v_a_x3f_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v_isExporting_boxed_2259_; lean_object* v_res_2260_; 
v_isExporting_boxed_2259_ = lean_unbox(v_isExporting_2253_);
v_res_2260_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2252_, v_isExporting_boxed_2259_, v___x_2254_, v___y_2255_, v___x_2256_, v_a_x3f_2257_);
lean_dec(v_a_x3f_2257_);
lean_dec(v___y_2255_);
lean_dec(v___y_2252_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object* v_declName_2261_, uint8_t v_isExporting_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v_env_2268_; lean_object* v___x_2269_; uint8_t v_isModule_2270_; 
v___x_2267_ = lean_st_ref_get(v___y_2265_);
v_env_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_env_2268_);
lean_dec(v___x_2267_);
v___x_2269_ = l_Lean_Environment_header(v_env_2268_);
v_isModule_2270_ = lean_ctor_get_uint8(v___x_2269_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2269_);
if (v_isModule_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_dec_ref(v_env_2268_);
v___x_2271_ = l_Lean_validateDefEqAttr(v_declName_2261_, v___y_2264_, v___y_2265_);
return v___x_2271_;
}
else
{
uint8_t v_isExporting_2272_; 
v_isExporting_2272_ = lean_ctor_get_uint8(v_env_2268_, sizeof(void*)*8);
lean_dec_ref(v_env_2268_);
if (v_isExporting_2262_ == 0)
{
if (v_isExporting_2272_ == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_validateDefEqAttr(v_declName_2261_, v___y_2264_, v___y_2265_);
return v___x_2338_;
}
else
{
goto v___jp_2273_;
}
}
else
{
if (v_isExporting_2272_ == 0)
{
goto v___jp_2273_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_validateDefEqAttr(v_declName_2261_, v___y_2264_, v___y_2265_);
return v___x_2339_;
}
}
v___jp_2273_:
{
lean_object* v___x_2274_; lean_object* v_env_2275_; lean_object* v_nextMacroScope_2276_; lean_object* v_ngen_2277_; lean_object* v_auxDeclNGen_2278_; lean_object* v_traceState_2279_; lean_object* v_messages_2280_; lean_object* v_infoState_2281_; lean_object* v_snapshotTasks_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2336_; 
v___x_2274_ = lean_st_ref_take(v___y_2265_);
v_env_2275_ = lean_ctor_get(v___x_2274_, 0);
v_nextMacroScope_2276_ = lean_ctor_get(v___x_2274_, 1);
v_ngen_2277_ = lean_ctor_get(v___x_2274_, 2);
v_auxDeclNGen_2278_ = lean_ctor_get(v___x_2274_, 3);
v_traceState_2279_ = lean_ctor_get(v___x_2274_, 4);
v_messages_2280_ = lean_ctor_get(v___x_2274_, 6);
v_infoState_2281_ = lean_ctor_get(v___x_2274_, 7);
v_snapshotTasks_2282_ = lean_ctor_get(v___x_2274_, 8);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v___x_2274_, 5);
lean_dec(v_unused_2337_);
v___x_2284_ = v___x_2274_;
v_isShared_2285_ = v_isSharedCheck_2336_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snapshotTasks_2282_);
lean_inc(v_infoState_2281_);
lean_inc(v_messages_2280_);
lean_inc(v_traceState_2279_);
lean_inc(v_auxDeclNGen_2278_);
lean_inc(v_ngen_2277_);
lean_inc(v_nextMacroScope_2276_);
lean_inc(v_env_2275_);
lean_dec(v___x_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2336_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2286_ = l_Lean_Environment_setExporting(v_env_2275_, v_isExporting_2262_);
v___x_2287_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 5, v___x_2287_);
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2289_ = v___x_2284_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_nextMacroScope_2276_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_ngen_2277_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_auxDeclNGen_2278_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_traceState_2279_);
lean_ctor_set(v_reuseFailAlloc_2335_, 5, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2335_, 6, v_messages_2280_);
lean_ctor_set(v_reuseFailAlloc_2335_, 7, v_infoState_2281_);
lean_ctor_set(v_reuseFailAlloc_2335_, 8, v_snapshotTasks_2282_);
v___x_2289_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_mctx_2292_; lean_object* v_zetaDeltaFVarIds_2293_; lean_object* v_postponed_2294_; lean_object* v_diag_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2333_; 
v___x_2290_ = lean_st_ref_put(v___y_2265_, v___x_2289_);
v___x_2291_ = lean_st_ref_take(v___y_2263_);
v_mctx_2292_ = lean_ctor_get(v___x_2291_, 0);
v_zetaDeltaFVarIds_2293_ = lean_ctor_get(v___x_2291_, 2);
v_postponed_2294_ = lean_ctor_get(v___x_2291_, 3);
v_diag_2295_ = lean_ctor_get(v___x_2291_, 4);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v___x_2291_, 1);
lean_dec(v_unused_2334_);
v___x_2297_ = v___x_2291_;
v_isShared_2298_ = v_isSharedCheck_2333_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_diag_2295_);
lean_inc(v_postponed_2294_);
lean_inc(v_zetaDeltaFVarIds_2293_);
lean_inc(v_mctx_2292_);
lean_dec(v___x_2291_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2333_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2299_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_mctx_2292_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_zetaDeltaFVarIds_2293_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_postponed_2294_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_diag_2295_);
v___x_2301_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; lean_object* v_r_2303_; 
v___x_2302_ = lean_st_ref_put(v___y_2263_, v___x_2301_);
v_r_2303_ = l_Lean_validateDefEqAttr(v_declName_2261_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v_r_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2320_; 
v_a_2304_ = lean_ctor_get(v_r_2303_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_r_2303_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2306_ = v_r_2303_;
v_isShared_2307_ = v_isSharedCheck_2320_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v_r_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2320_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
lean_inc(v_a_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 1);
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v___x_2310_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2265_, v_isExporting_2272_, v___x_2287_, v___y_2263_, v___x_2299_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2310_, 0);
lean_dec(v_unused_2318_);
v___x_2312_ = v___x_2310_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v___x_2310_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_a_2304_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2304_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_a_2321_ = lean_ctor_get(v_r_2303_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v_r_2303_, 1);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2265_, v_isExporting_2272_, v___x_2287_, v___y_2263_, v___x_2299_, v___x_2322_);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2323_, 0);
lean_dec(v_unused_2331_);
v___x_2325_ = v___x_2323_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v___x_2323_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 1);
lean_ctor_set(v___x_2325_, 0, v_a_2321_);
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2321_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object* v_declName_2340_, lean_object* v_isExporting_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v_isExporting_boxed_2346_; lean_object* v_res_2347_; 
v_isExporting_boxed_2346_ = lean_unbox(v_isExporting_2341_);
v_res_2347_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2340_, v_isExporting_boxed_2346_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object* v_declName_2348_, uint8_t v_isExporting_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2348_, v_isExporting_2349_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object* v_declName_2356_, lean_object* v_isExporting_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v_isExporting_boxed_2363_; lean_object* v_res_2364_; 
v_isExporting_boxed_2363_ = lean_unbox(v_isExporting_2357_);
v_res_2364_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2356_, v_isExporting_boxed_2363_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* v_lhs_2365_, lean_object* v_rhs_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___y_2373_; lean_object* v___x_2390_; uint8_t v_transparency_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2390_ = l_Lean_Meta_Context_config(v___y_2367_);
v_transparency_2391_ = lean_ctor_get_uint8(v___x_2390_, 9);
lean_dec_ref(v___x_2390_);
v___x_2392_ = 5;
v___x_2393_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v_keyedConfig_2394_; uint8_t v_trackZetaDelta_2395_; lean_object* v_zetaDeltaSet_2396_; lean_object* v_lctx_2397_; lean_object* v_localInstances_2398_; lean_object* v_defEqCtx_x3f_2399_; lean_object* v_synthPendingDepth_2400_; lean_object* v_customCanUnfoldPredicate_x3f_2401_; uint8_t v_univApprox_2402_; uint8_t v_inTypeClassResolution_2403_; uint8_t v_cacheInferType_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_keyedConfig_2394_ = lean_ctor_get(v___y_2367_, 0);
v_trackZetaDelta_2395_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7);
v_zetaDeltaSet_2396_ = lean_ctor_get(v___y_2367_, 1);
v_lctx_2397_ = lean_ctor_get(v___y_2367_, 2);
v_localInstances_2398_ = lean_ctor_get(v___y_2367_, 3);
v_defEqCtx_x3f_2399_ = lean_ctor_get(v___y_2367_, 4);
v_synthPendingDepth_2400_ = lean_ctor_get(v___y_2367_, 5);
v_customCanUnfoldPredicate_x3f_2401_ = lean_ctor_get(v___y_2367_, 6);
v_univApprox_2402_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2403_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 2);
v_cacheInferType_2404_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2394_);
v___x_2405_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2392_, v_keyedConfig_2394_);
lean_inc(v_customCanUnfoldPredicate_x3f_2401_);
lean_inc(v_synthPendingDepth_2400_);
lean_inc(v_defEqCtx_x3f_2399_);
lean_inc_ref(v_localInstances_2398_);
lean_inc_ref(v_lctx_2397_);
lean_inc(v_zetaDeltaSet_2396_);
v___x_2406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v_zetaDeltaSet_2396_);
lean_ctor_set(v___x_2406_, 2, v_lctx_2397_);
lean_ctor_set(v___x_2406_, 3, v_localInstances_2398_);
lean_ctor_set(v___x_2406_, 4, v_defEqCtx_x3f_2399_);
lean_ctor_set(v___x_2406_, 5, v_synthPendingDepth_2400_);
lean_ctor_set(v___x_2406_, 6, v_customCanUnfoldPredicate_x3f_2401_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7, v_trackZetaDelta_2395_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 1, v_univApprox_2402_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2403_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 3, v_cacheInferType_2404_);
v___x_2407_ = l_Lean_Meta_isExprDefEq(v_lhs_2365_, v_rhs_2366_, v___x_2406_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec_ref_known(v___x_2406_, 7);
v___y_2373_ = v___x_2407_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Meta_isExprDefEq(v_lhs_2365_, v_rhs_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
v___y_2373_ = v___x_2408_;
goto v___jp_2372_;
}
v___jp_2372_:
{
if (lean_obj_tag(v___y_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v_a_2374_ = lean_ctor_get(v___y_2373_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___y_2373_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___y_2373_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___y_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_a_2382_ = lean_ctor_get(v___y_2373_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___y_2373_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___y_2373_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___y_2373_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* v_lhs_2409_, lean_object* v_rhs_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2409_, v_rhs_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* v_declName_2423_, lean_object* v___f_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___x_2440_; 
lean_inc(v_declName_2423_);
v___x_2440_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_declName_2423_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc_n(v_a_2441_, 2);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = 1;
v___x_2443_ = l_Lean_ConstantInfo_value_x3f(v_a_2441_, v___x_2442_);
if (lean_obj_tag(v___x_2443_) == 1)
{
lean_object* v_val_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_val_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_ConstantInfo_type(v_a_2441_);
lean_dec(v_a_2441_);
v___x_2446_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v___x_2445_, v_val_2444_, v___y_2428_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; uint8_t v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = lean_unbox(v_a_2447_);
if (v___x_2448_ == 0)
{
lean_dec(v_a_2447_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___f_2424_);
lean_dec(v_declName_2423_);
goto v___jp_2437_;
}
else
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v___x_2445_, v___f_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___y_2456_; lean_object* v___y_2458_; lean_object* v___y_2459_; uint8_t v___y_2460_; uint8_t v___y_2472_; uint8_t v___x_2477_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2477_ = l_Lean_isPrivateName(v_declName_2423_);
if (v___x_2477_ == 0)
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
v___y_2472_ = v___x_2478_;
goto v___jp_2471_;
}
else
{
uint8_t v___x_2479_; 
lean_dec(v_a_2447_);
v___x_2479_ = 0;
v___y_2472_ = v___x_2479_;
goto v___jp_2471_;
}
v___jp_2451_:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_unbox(v_a_2450_);
lean_dec(v_a_2450_);
if (v___x_2452_ == 0)
{
v___y_2431_ = v___y_2425_;
v___y_2432_ = v___y_2426_;
v___y_2433_ = v___y_2427_;
v___y_2434_ = v___y_2428_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = l_Lean_defeqAttr;
lean_inc(v_declName_2423_);
v___x_2454_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2453_, v_declName_2423_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref_known(v___x_2454_, 1);
v___y_2431_ = v___y_2425_;
v___y_2432_ = v___y_2426_;
v___y_2433_ = v___y_2427_;
v___y_2434_ = v___y_2428_;
goto v___jp_2430_;
}
else
{
lean_dec(v_declName_2423_);
return v___x_2454_;
}
}
}
v___jp_2455_:
{
if (lean_obj_tag(v___y_2456_) == 0)
{
lean_dec_ref_known(v___y_2456_, 1);
goto v___jp_2451_;
}
else
{
lean_dec(v_a_2450_);
lean_dec(v_declName_2423_);
return v___y_2456_;
}
}
v___jp_2457_:
{
if (v___y_2460_ == 0)
{
uint8_t v___x_2461_; 
lean_dec_ref(v___y_2458_);
v___x_2461_ = lean_unbox(v_a_2450_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2462_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__1, &l_Lean_inferDefEqAttr___lam__1___closed__1_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__1);
lean_inc(v_declName_2423_);
v___x_2463_ = l_Lean_MessageData_ofName(v_declName_2423_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__3, &l_Lean_inferDefEqAttr___lam__1___closed__3_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__3);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_Exception_toMessageData(v___y_2459_);
v___x_2468_ = l_Lean_indentD(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v___x_2469_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
v___y_2456_ = v___x_2470_;
goto v___jp_2455_;
}
else
{
lean_dec_ref(v___y_2459_);
goto v___jp_2451_;
}
}
else
{
lean_dec_ref(v___y_2459_);
v___y_2456_ = v___y_2458_;
goto v___jp_2455_;
}
}
v___jp_2471_:
{
lean_object* v___x_2473_; 
lean_inc(v_declName_2423_);
v___x_2473_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2423_, v___y_2472_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2473_) == 0)
{
v___y_2456_ = v___x_2473_;
goto v___jp_2455_;
}
else
{
lean_object* v_a_2474_; uint8_t v___x_2475_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
v___x_2475_ = l_Lean_Exception_isInterrupt(v_a_2474_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
lean_inc(v_a_2474_);
v___x_2476_ = l_Lean_Exception_isRuntime(v_a_2474_);
v___y_2458_ = v___x_2473_;
v___y_2459_ = v_a_2474_;
v___y_2460_ = v___x_2476_;
goto v___jp_2457_;
}
else
{
v___y_2458_ = v___x_2473_;
v___y_2459_ = v_a_2474_;
v___y_2460_ = v___x_2475_;
goto v___jp_2457_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2447_);
lean_dec(v_declName_2423_);
v_a_2480_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2449_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2449_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___f_2424_);
lean_dec(v_declName_2423_);
v_a_2488_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2446_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2446_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_dec(v___x_2443_);
lean_dec(v_a_2441_);
lean_dec_ref(v___f_2424_);
lean_dec(v_declName_2423_);
goto v___jp_2437_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v___f_2424_);
lean_dec(v_declName_2423_);
v_a_2496_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2440_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2440_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
v___jp_2430_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = l_Lean_backwardDefeqAttr;
v___x_2436_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2435_, v_declName_2423_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
v___jp_2437_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object* v_declName_2504_, lean_object* v___f_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2504_, v___f_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object* v_declName_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___f_2519_; lean_object* v___f_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; 
v___f_2519_ = ((lean_object*)(l_Lean_inferDefEqAttr___closed__0));
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2520_, 0, v_declName_2513_);
lean_closure_set(v___f_2520_, 1, v___f_2519_);
v___x_2521_ = 1;
v___x_2522_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___f_2520_, v___x_2521_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object* v_declName_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_inferDefEqAttr(v_declName_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_2530_, lean_object* v_attrName_2531_, lean_object* v_declName_2532_, lean_object* v_asyncPrefix_x3f_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_2531_, v_declName_2532_, v_asyncPrefix_x3f_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_attrName_2541_, lean_object* v_declName_2542_, lean_object* v_asyncPrefix_x3f_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_2540_, v_attrName_2541_, v_declName_2542_, v_asyncPrefix_x3f_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object* v_00_u03b1_2550_, lean_object* v_attrName_2551_, lean_object* v_declName_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_2551_, v_declName_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_attrName_2560_, lean_object* v_declName_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_2559_, v_attrName_2560_, v_declName_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object* v_00_u03b1_2568_, lean_object* v_constName_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2576_, lean_object* v_constName_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_2576_, v_constName_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object* v_00_u03b1_2584_, lean_object* v_ref_2585_, lean_object* v_constName_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2585_, v_constName_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2593_, lean_object* v_ref_2594_, lean_object* v_constName_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_2593_, v_ref_2594_, v_constName_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_ref_2594_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object* v_00_u03b1_2602_, lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v_declHint_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2603_, v_msg_2604_, v_declHint_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2612_, lean_object* v_ref_2613_, lean_object* v_msg_2614_, lean_object* v_declHint_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_2612_, v_ref_2613_, v_msg_2614_, v_declHint_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v_ref_2613_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(lean_object* v_msg_2622_, lean_object* v_declHint_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_2622_, v_declHint_2623_, v___y_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_2630_, lean_object* v_declHint_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(v_msg_2630_, v_declHint_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_2638_, lean_object* v_ref_2639_, lean_object* v_msg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2639_, v_msg_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_ref_2648_, lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_2647_, v_ref_2648_, v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_ref_2648_);
return v_res_2655_;
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
