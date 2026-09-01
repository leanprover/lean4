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
lean_object* v___y_135_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_192_; lean_object* v_toCold_193_; lean_object* v_options_194_; lean_object* v_currRecDepth_195_; lean_object* v_ref_196_; lean_object* v_currNamespace_197_; lean_object* v_openDecls_198_; lean_object* v_initHeartbeats_199_; lean_object* v_maxHeartbeats_200_; lean_object* v_currMacroScope_201_; uint8_t v_suppressElabErrors_202_; lean_object* v_env_203_; uint8_t v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v_toCold_211_; lean_object* v_currRecDepth_212_; lean_object* v_ref_213_; lean_object* v_currNamespace_214_; lean_object* v_openDecls_215_; lean_object* v_initHeartbeats_216_; lean_object* v_maxHeartbeats_217_; lean_object* v_currMacroScope_218_; uint8_t v_suppressElabErrors_219_; lean_object* v___y_220_; uint8_t v___y_243_; uint8_t v___x_264_; 
v___x_192_ = lean_st_ref_get(v_a_132_);
v_toCold_193_ = lean_ctor_get(v_a_131_, 0);
v_options_194_ = lean_ctor_get(v_a_131_, 1);
v_currRecDepth_195_ = lean_ctor_get(v_a_131_, 2);
v_ref_196_ = lean_ctor_get(v_a_131_, 4);
v_currNamespace_197_ = lean_ctor_get(v_a_131_, 5);
v_openDecls_198_ = lean_ctor_get(v_a_131_, 6);
v_initHeartbeats_199_ = lean_ctor_get(v_a_131_, 7);
v_maxHeartbeats_200_ = lean_ctor_get(v_a_131_, 8);
v_currMacroScope_201_ = lean_ctor_get(v_a_131_, 9);
v_suppressElabErrors_202_ = lean_ctor_get_uint8(v_a_131_, sizeof(void*)*10 + 1);
v_env_203_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_203_);
lean_dec(v___x_192_);
v___x_204_ = 1;
v___x_205_ = l_Lean_Meta_smartUnfolding;
v___x_206_ = 0;
lean_inc_ref(v_options_194_);
v___x_207_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_options_194_, v___x_205_, v___x_206_);
v___x_208_ = l_Lean_diagnostics;
v___x_209_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v___x_207_, v___x_208_);
v___x_264_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_203_);
lean_dec_ref(v_env_203_);
if (v___x_209_ == 0)
{
if (v___x_264_ == 0)
{
v_toCold_211_ = v_toCold_193_;
v_currRecDepth_212_ = v_currRecDepth_195_;
v_ref_213_ = v_ref_196_;
v_currNamespace_214_ = v_currNamespace_197_;
v_openDecls_215_ = v_openDecls_198_;
v_initHeartbeats_216_ = v_initHeartbeats_199_;
v_maxHeartbeats_217_ = v_maxHeartbeats_200_;
v_currMacroScope_218_ = v_currMacroScope_201_;
v_suppressElabErrors_219_ = v_suppressElabErrors_202_;
v___y_220_ = v_a_132_;
goto v___jp_210_;
}
else
{
v___y_243_ = v___x_209_;
goto v___jp_242_;
}
}
else
{
v___y_243_ = v___x_264_;
goto v___jp_242_;
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
v___x_178_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v___x_177_, v_a_130_, v___y_154_, v___y_153_);
lean_dec_ref(v___y_154_);
lean_dec_ref_known(v___x_177_, 7);
v___y_135_ = v___x_178_;
goto v___jp_134_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v_a_129_, v_a_130_, v___y_154_, v___y_153_);
lean_dec_ref(v___y_154_);
v___y_135_ = v___x_179_;
goto v___jp_134_;
}
}
else
{
lean_object* v___x_181_; 
lean_dec_ref(v___y_154_);
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
lean_dec_ref(v___y_154_);
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
v___jp_210_:
{
lean_object* v___x_221_; uint8_t v_transparency_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_221_ = l_Lean_Meta_Context_config(v_a_129_);
v_transparency_222_ = lean_ctor_get_uint8(v___x_221_, 9);
lean_dec_ref(v___x_221_);
v___x_223_ = l_Lean_maxRecDepth;
v___x_224_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(v___x_207_, v___x_223_);
lean_inc(v_currMacroScope_218_);
lean_inc(v_maxHeartbeats_217_);
lean_inc(v_initHeartbeats_216_);
lean_inc(v_openDecls_215_);
lean_inc(v_currNamespace_214_);
lean_inc(v_ref_213_);
lean_inc(v_currRecDepth_212_);
lean_inc_ref(v_toCold_211_);
v___x_225_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_225_, 0, v_toCold_211_);
lean_ctor_set(v___x_225_, 1, v___x_207_);
lean_ctor_set(v___x_225_, 2, v_currRecDepth_212_);
lean_ctor_set(v___x_225_, 3, v___x_224_);
lean_ctor_set(v___x_225_, 4, v_ref_213_);
lean_ctor_set(v___x_225_, 5, v_currNamespace_214_);
lean_ctor_set(v___x_225_, 6, v_openDecls_215_);
lean_ctor_set(v___x_225_, 7, v_initHeartbeats_216_);
lean_ctor_set(v___x_225_, 8, v_maxHeartbeats_217_);
lean_ctor_set(v___x_225_, 9, v_currMacroScope_218_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*10, v___x_209_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*10 + 1, v_suppressElabErrors_219_);
v___x_226_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_222_, v___x_204_);
if (v___x_226_ == 0)
{
lean_object* v_keyedConfig_227_; uint8_t v_trackZetaDelta_228_; lean_object* v_zetaDeltaSet_229_; lean_object* v_lctx_230_; lean_object* v_localInstances_231_; lean_object* v_defEqCtx_x3f_232_; lean_object* v_synthPendingDepth_233_; lean_object* v_customCanUnfoldPredicate_x3f_234_; uint8_t v_univApprox_235_; uint8_t v_inTypeClassResolution_236_; uint8_t v_cacheInferType_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_keyedConfig_227_ = lean_ctor_get(v_a_129_, 0);
v_trackZetaDelta_228_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7);
v_zetaDeltaSet_229_ = lean_ctor_get(v_a_129_, 1);
v_lctx_230_ = lean_ctor_get(v_a_129_, 2);
v_localInstances_231_ = lean_ctor_get(v_a_129_, 3);
v_defEqCtx_x3f_232_ = lean_ctor_get(v_a_129_, 4);
v_synthPendingDepth_233_ = lean_ctor_get(v_a_129_, 5);
v_customCanUnfoldPredicate_x3f_234_ = lean_ctor_get(v_a_129_, 6);
v_univApprox_235_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_236_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 2);
v_cacheInferType_237_ = lean_ctor_get_uint8(v_a_129_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_227_);
v___x_238_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_204_, v_keyedConfig_227_);
lean_inc(v_customCanUnfoldPredicate_x3f_234_);
lean_inc(v_synthPendingDepth_233_);
lean_inc(v_defEqCtx_x3f_232_);
lean_inc_ref(v_localInstances_231_);
lean_inc_ref(v_lctx_230_);
lean_inc(v_zetaDeltaSet_229_);
v___x_239_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_zetaDeltaSet_229_);
lean_ctor_set(v___x_239_, 2, v_lctx_230_);
lean_ctor_set(v___x_239_, 3, v_localInstances_231_);
lean_ctor_set(v___x_239_, 4, v_defEqCtx_x3f_232_);
lean_ctor_set(v___x_239_, 5, v_synthPendingDepth_233_);
lean_ctor_set(v___x_239_, 6, v_customCanUnfoldPredicate_x3f_234_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*7, v_trackZetaDelta_228_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*7 + 1, v_univApprox_235_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*7 + 2, v_inTypeClassResolution_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*7 + 3, v_cacheInferType_237_);
lean_inc_ref(v_e2_128_);
lean_inc_ref(v_e1_127_);
v___x_240_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v___x_239_, v_a_130_, v___x_225_, v___y_220_);
lean_dec_ref_known(v___x_239_, 7);
v___y_153_ = v___y_220_;
v___y_154_ = v___x_225_;
v___y_155_ = v___x_240_;
goto v___jp_152_;
}
else
{
lean_object* v___x_241_; 
lean_inc_ref(v_e2_128_);
lean_inc_ref(v_e1_127_);
v___x_241_ = l_Lean_Meta_isExprDefEq(v_e1_127_, v_e2_128_, v_a_129_, v_a_130_, v___x_225_, v___y_220_);
v___y_153_ = v___y_220_;
v___y_154_ = v___x_225_;
v___y_155_ = v___x_241_;
goto v___jp_152_;
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_object* v___x_244_; lean_object* v_env_245_; lean_object* v_nextMacroScope_246_; lean_object* v_ngen_247_; lean_object* v_auxDeclNGen_248_; lean_object* v_traceState_249_; lean_object* v_messages_250_; lean_object* v_infoState_251_; lean_object* v_snapshotTasks_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v___x_244_ = lean_st_ref_take(v_a_132_);
v_env_245_ = lean_ctor_get(v___x_244_, 0);
v_nextMacroScope_246_ = lean_ctor_get(v___x_244_, 1);
v_ngen_247_ = lean_ctor_get(v___x_244_, 2);
v_auxDeclNGen_248_ = lean_ctor_get(v___x_244_, 3);
v_traceState_249_ = lean_ctor_get(v___x_244_, 4);
v_messages_250_ = lean_ctor_get(v___x_244_, 6);
v_infoState_251_ = lean_ctor_get(v___x_244_, 7);
v_snapshotTasks_252_ = lean_ctor_get(v___x_244_, 8);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_244_, 5);
lean_dec(v_unused_263_);
v___x_254_ = v___x_244_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snapshotTasks_252_);
lean_inc(v_infoState_251_);
lean_inc(v_messages_250_);
lean_inc(v_traceState_249_);
lean_inc(v_auxDeclNGen_248_);
lean_inc(v_ngen_247_);
lean_inc(v_nextMacroScope_246_);
lean_inc(v_env_245_);
lean_dec(v___x_244_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = l_Lean_Kernel_enableDiag(v_env_245_, v___x_209_);
v___x_257_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 5, v___x_257_);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_nextMacroScope_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_ngen_247_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_auxDeclNGen_248_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_traceState_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 5, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 6, v_messages_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 7, v_infoState_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 8, v_snapshotTasks_252_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_st_ref_put(v_a_132_, v___x_259_);
v_toCold_211_ = v_toCold_193_;
v_currRecDepth_212_ = v_currRecDepth_195_;
v_ref_213_ = v_ref_196_;
v_currNamespace_214_ = v_currNamespace_197_;
v_openDecls_215_ = v_openDecls_198_;
v_initHeartbeats_216_ = v_initHeartbeats_199_;
v_maxHeartbeats_217_ = v_maxHeartbeats_200_;
v_currMacroScope_218_ = v_currMacroScope_201_;
v_suppressElabErrors_219_ = v_suppressElabErrors_202_;
v___y_220_ = v_a_132_;
goto v___jp_210_;
}
}
}
else
{
v_toCold_211_ = v_toCold_193_;
v_currRecDepth_212_ = v_currRecDepth_195_;
v_ref_213_ = v_ref_196_;
v_currNamespace_214_ = v_currNamespace_197_;
v_openDecls_215_ = v_openDecls_198_;
v_initHeartbeats_216_ = v_initHeartbeats_199_;
v_maxHeartbeats_217_ = v_maxHeartbeats_200_;
v_currMacroScope_218_ = v_currMacroScope_201_;
v_suppressElabErrors_219_ = v_suppressElabErrors_202_;
v___y_220_ = v_a_132_;
goto v___jp_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(lean_object* v_e1_265_, lean_object* v_e2_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_e1_265_, v_e2_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(lean_object* v_k_273_, lean_object* v_b_274_, lean_object* v_c_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_281_ = lean_apply_7(v_k_273_, v_b_274_, v_c_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, lean_box(0));
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v_c_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_282_, v_b_283_, v_c_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(lean_object* v_type_291_, lean_object* v_k_292_, uint8_t v_cleanupAnnotations_293_, uint8_t v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_300_, 0, v_k_292_);
v___x_301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_291_, v___f_300_, v_cleanupAnnotations_293_, v_whnfType_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
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
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_301_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_301_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(lean_object* v_type_318_, lean_object* v_k_319_, lean_object* v_cleanupAnnotations_320_, lean_object* v_whnfType_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_327_; uint8_t v_whnfType_boxed_328_; lean_object* v_res_329_; 
v_cleanupAnnotations_boxed_327_ = lean_unbox(v_cleanupAnnotations_320_);
v_whnfType_boxed_328_ = lean_unbox(v_whnfType_321_);
v_res_329_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_318_, v_k_319_, v_cleanupAnnotations_boxed_327_, v_whnfType_boxed_328_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_object* v_00_u03b1_330_, lean_object* v_type_331_, lean_object* v_k_332_, uint8_t v_cleanupAnnotations_333_, uint8_t v_whnfType_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_331_, v_k_332_, v_cleanupAnnotations_333_, v_whnfType_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(lean_object* v_00_u03b1_341_, lean_object* v_type_342_, lean_object* v_k_343_, lean_object* v_cleanupAnnotations_344_, lean_object* v_whnfType_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_351_; uint8_t v_whnfType_boxed_352_; lean_object* v_res_353_; 
v_cleanupAnnotations_boxed_351_ = lean_unbox(v_cleanupAnnotations_344_);
v_whnfType_boxed_352_ = lean_unbox(v_whnfType_345_);
v_res_353_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(v_00_u03b1_341_, v_type_342_, v_k_343_, v_cleanupAnnotations_boxed_351_, v_whnfType_boxed_352_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(lean_object* v_msgData_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_env_361_; lean_object* v___x_362_; lean_object* v_mctx_363_; lean_object* v_lctx_364_; lean_object* v_options_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_360_ = lean_st_ref_get(v___y_358_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v___x_362_ = lean_st_ref_get(v___y_356_);
v_mctx_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_mctx_363_);
lean_dec(v___x_362_);
v_lctx_364_ = lean_ctor_get(v___y_355_, 2);
v_options_365_ = lean_ctor_get(v___y_357_, 1);
lean_inc_ref(v_options_365_);
lean_inc_ref(v_lctx_364_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_361_);
lean_ctor_set(v___x_366_, 1, v_mctx_363_);
lean_ctor_set(v___x_366_, 2, v_lctx_364_);
lean_ctor_set(v___x_366_, 3, v_options_365_);
v___x_367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_msgData_354_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(lean_object* v_msg_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_ref_382_; lean_object* v___x_383_; lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_ref_382_ = lean_ctor_get(v___y_379_, 4);
v___x_383_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msg_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
lean_inc(v_ref_382_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_ref_382_);
lean_ctor_set(v___x_388_, 1, v_a_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 1);
lean_ctor_set(v___x_386_, 0, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_399_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(lean_object* v_k_406_, lean_object* v_x_407_, lean_object* v_type_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
lean_inc(v___y_412_);
lean_inc_ref(v___y_411_);
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
v___x_414_ = lean_whnf(v_type_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = l_Lean_Expr_isAppOfArity(v_a_415_, v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_k_406_);
v___x_419_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3);
v___x_420_ = lean_unsigned_to_nat(30u);
v___x_421_ = l_Lean_inlineExpr(v_a_415_, v___x_420_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_422_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = l_Lean_Expr_appFn_x21(v_a_415_);
v___x_425_ = l_Lean_Expr_appArg_x21(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = l_Lean_Expr_appArg_x21(v_a_415_);
lean_dec(v_a_415_);
lean_inc(v___y_412_);
lean_inc_ref(v___y_411_);
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
v___x_427_ = lean_apply_7(v_k_406_, v___x_425_, v___x_426_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, lean_box(0));
return v___x_427_;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_k_406_);
v_a_428_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_414_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_414_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(lean_object* v_k_436_, lean_object* v_x_437_, lean_object* v_type_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(v_k_436_, v_x_437_, v_type_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec_ref(v_x_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(lean_object* v_type_445_, lean_object* v_k_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___y_453_; lean_object* v___x_470_; uint8_t v_transparency_471_; lean_object* v___f_472_; uint8_t v___x_473_; uint8_t v___x_474_; uint8_t v___x_475_; 
v___x_470_ = l_Lean_Meta_Context_config(v_a_447_);
v_transparency_471_ = lean_ctor_get_uint8(v___x_470_, 9);
lean_dec_ref(v___x_470_);
v___f_472_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_472_, 0, v_k_446_);
v___x_473_ = 0;
v___x_474_ = 0;
v___x_475_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_471_, v___x_473_);
if (v___x_475_ == 0)
{
lean_object* v_keyedConfig_476_; uint8_t v_trackZetaDelta_477_; lean_object* v_zetaDeltaSet_478_; lean_object* v_lctx_479_; lean_object* v_localInstances_480_; lean_object* v_defEqCtx_x3f_481_; lean_object* v_synthPendingDepth_482_; lean_object* v_customCanUnfoldPredicate_x3f_483_; uint8_t v_univApprox_484_; uint8_t v_inTypeClassResolution_485_; uint8_t v_cacheInferType_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_keyedConfig_476_ = lean_ctor_get(v_a_447_, 0);
v_trackZetaDelta_477_ = lean_ctor_get_uint8(v_a_447_, sizeof(void*)*7);
v_zetaDeltaSet_478_ = lean_ctor_get(v_a_447_, 1);
v_lctx_479_ = lean_ctor_get(v_a_447_, 2);
v_localInstances_480_ = lean_ctor_get(v_a_447_, 3);
v_defEqCtx_x3f_481_ = lean_ctor_get(v_a_447_, 4);
v_synthPendingDepth_482_ = lean_ctor_get(v_a_447_, 5);
v_customCanUnfoldPredicate_x3f_483_ = lean_ctor_get(v_a_447_, 6);
v_univApprox_484_ = lean_ctor_get_uint8(v_a_447_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_485_ = lean_ctor_get_uint8(v_a_447_, sizeof(void*)*7 + 2);
v_cacheInferType_486_ = lean_ctor_get_uint8(v_a_447_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_476_);
v___x_487_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_473_, v_keyedConfig_476_);
lean_inc(v_customCanUnfoldPredicate_x3f_483_);
lean_inc(v_synthPendingDepth_482_);
lean_inc(v_defEqCtx_x3f_481_);
lean_inc_ref(v_localInstances_480_);
lean_inc_ref(v_lctx_479_);
lean_inc(v_zetaDeltaSet_478_);
v___x_488_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_zetaDeltaSet_478_);
lean_ctor_set(v___x_488_, 2, v_lctx_479_);
lean_ctor_set(v___x_488_, 3, v_localInstances_480_);
lean_ctor_set(v___x_488_, 4, v_defEqCtx_x3f_481_);
lean_ctor_set(v___x_488_, 5, v_synthPendingDepth_482_);
lean_ctor_set(v___x_488_, 6, v_customCanUnfoldPredicate_x3f_483_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7, v_trackZetaDelta_477_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 1, v_univApprox_484_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 2, v_inTypeClassResolution_485_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 3, v_cacheInferType_486_);
v___x_489_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_445_, v___f_472_, v___x_474_, v___x_474_, v___x_488_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref_known(v___x_488_, 7);
v___y_453_ = v___x_489_;
goto v___jp_452_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_445_, v___f_472_, v___x_474_, v___x_474_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
v___y_453_ = v___x_490_;
goto v___jp_452_;
}
v___jp_452_:
{
if (lean_obj_tag(v___y_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___y_453_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___y_453_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___y_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___y_453_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___y_453_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___y_453_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___y_453_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(lean_object* v_type_491_, lean_object* v_k_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_491_, v_k_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_object* v_00_u03b1_499_, lean_object* v_type_500_, lean_object* v_k_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_500_, v_k_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(lean_object* v_00_u03b1_508_, lean_object* v_type_509_, lean_object* v_k_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(v_00_u03b1_508_, v_type_509_, v_k_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_object* v_00_u03b1_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(lean_object* v_00_u03b1_525_, lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(v_00_u03b1_525_, v_msg_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(lean_object* v___y_533_, uint8_t v_isExporting_534_, lean_object* v___x_535_, lean_object* v___y_536_, lean_object* v___x_537_, lean_object* v_a_x3f_538_){
_start:
{
lean_object* v___x_540_; lean_object* v_env_541_; lean_object* v_nextMacroScope_542_; lean_object* v_ngen_543_; lean_object* v_auxDeclNGen_544_; lean_object* v_traceState_545_; lean_object* v_messages_546_; lean_object* v_infoState_547_; lean_object* v_snapshotTasks_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_573_; 
v___x_540_ = lean_st_ref_take(v___y_533_);
v_env_541_ = lean_ctor_get(v___x_540_, 0);
v_nextMacroScope_542_ = lean_ctor_get(v___x_540_, 1);
v_ngen_543_ = lean_ctor_get(v___x_540_, 2);
v_auxDeclNGen_544_ = lean_ctor_get(v___x_540_, 3);
v_traceState_545_ = lean_ctor_get(v___x_540_, 4);
v_messages_546_ = lean_ctor_get(v___x_540_, 6);
v_infoState_547_ = lean_ctor_get(v___x_540_, 7);
v_snapshotTasks_548_ = lean_ctor_get(v___x_540_, 8);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_540_, 5);
lean_dec(v_unused_574_);
v___x_550_ = v___x_540_;
v_isShared_551_ = v_isSharedCheck_573_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snapshotTasks_548_);
lean_inc(v_infoState_547_);
lean_inc(v_messages_546_);
lean_inc(v_traceState_545_);
lean_inc(v_auxDeclNGen_544_);
lean_inc(v_ngen_543_);
lean_inc(v_nextMacroScope_542_);
lean_inc(v_env_541_);
lean_dec(v___x_540_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_573_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Environment_setExporting(v_env_541_, v_isExporting_534_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 5, v___x_535_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_542_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_543_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_544_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_545_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_messages_546_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_infoState_547_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_snapshotTasks_548_);
v___x_554_ = v_reuseFailAlloc_572_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_mctx_557_; lean_object* v_zetaDeltaFVarIds_558_; lean_object* v_postponed_559_; lean_object* v_diag_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_570_; 
v___x_555_ = lean_st_ref_put(v___y_533_, v___x_554_);
v___x_556_ = lean_st_ref_take(v___y_536_);
v_mctx_557_ = lean_ctor_get(v___x_556_, 0);
v_zetaDeltaFVarIds_558_ = lean_ctor_get(v___x_556_, 2);
v_postponed_559_ = lean_ctor_get(v___x_556_, 3);
v_diag_560_ = lean_ctor_get(v___x_556_, 4);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v___x_556_, 1);
lean_dec(v_unused_571_);
v___x_562_ = v___x_556_;
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_diag_560_);
lean_inc(v_postponed_559_);
lean_inc(v_zetaDeltaFVarIds_558_);
lean_inc(v_mctx_557_);
lean_dec(v___x_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_537_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_mctx_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_zetaDeltaFVarIds_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_postponed_559_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_diag_560_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_st_ref_put(v___y_536_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___y_575_, lean_object* v_isExporting_576_, lean_object* v___x_577_, lean_object* v___y_578_, lean_object* v___x_579_, lean_object* v_a_x3f_580_, lean_object* v___y_581_){
_start:
{
uint8_t v_isExporting_boxed_582_; lean_object* v_res_583_; 
v_isExporting_boxed_582_ = lean_unbox(v_isExporting_576_);
v_res_583_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_575_, v_isExporting_boxed_582_, v___x_577_, v___y_578_, v___x_579_, v_a_x3f_580_);
lean_dec(v_a_x3f_580_);
lean_dec(v___y_578_);
lean_dec(v___y_575_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_585_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
lean_ctor_set(v___x_585_, 4, v___x_584_);
lean_ctor_set(v___x_585_, 5, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object* v_x_586_, uint8_t v_isExporting_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_env_594_; lean_object* v___x_595_; uint8_t v_isModule_596_; 
v___x_593_ = lean_st_ref_get(v___y_591_);
v_env_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_ref(v_env_594_);
lean_dec(v___x_593_);
v___x_595_ = l_Lean_Environment_header(v_env_594_);
v_isModule_596_ = lean_ctor_get_uint8(v___x_595_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_595_);
if (v_isModule_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_env_594_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
v___x_597_ = lean_apply_5(v_x_586_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, lean_box(0));
return v___x_597_;
}
else
{
uint8_t v_isExporting_598_; 
v_isExporting_598_ = lean_ctor_get_uint8(v_env_594_, sizeof(void*)*8);
lean_dec_ref(v_env_594_);
if (v_isExporting_587_ == 0)
{
if (v_isExporting_598_ == 0)
{
lean_object* v___x_664_; 
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
v___x_664_ = lean_apply_5(v_x_586_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, lean_box(0));
return v___x_664_;
}
else
{
goto v___jp_599_;
}
}
else
{
if (v_isExporting_598_ == 0)
{
goto v___jp_599_;
}
else
{
lean_object* v___x_665_; 
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
v___x_665_ = lean_apply_5(v_x_586_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, lean_box(0));
return v___x_665_;
}
}
v___jp_599_:
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_traceState_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_662_; 
v___x_600_ = lean_st_ref_take(v___y_591_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_600_, 1);
v_ngen_603_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_600_, 3);
v_traceState_605_ = lean_ctor_get(v___x_600_, 4);
v_messages_606_ = lean_ctor_get(v___x_600_, 6);
v_infoState_607_ = lean_ctor_get(v___x_600_, 7);
v_snapshotTasks_608_ = lean_ctor_get(v___x_600_, 8);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_600_, 5);
lean_dec(v_unused_663_);
v___x_610_ = v___x_600_;
v_isShared_611_ = v_isSharedCheck_662_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_600_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_662_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_612_ = l_Lean_Environment_setExporting(v_env_601_, v_isExporting_587_);
v___x_613_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 5, v___x_613_);
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_traceState_605_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_snapshotTasks_608_);
v___x_615_ = v_reuseFailAlloc_661_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_mctx_618_; lean_object* v_zetaDeltaFVarIds_619_; lean_object* v_postponed_620_; lean_object* v_diag_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_659_; 
v___x_616_ = lean_st_ref_put(v___y_591_, v___x_615_);
v___x_617_ = lean_st_ref_take(v___y_589_);
v_mctx_618_ = lean_ctor_get(v___x_617_, 0);
v_zetaDeltaFVarIds_619_ = lean_ctor_get(v___x_617_, 2);
v_postponed_620_ = lean_ctor_get(v___x_617_, 3);
v_diag_621_ = lean_ctor_get(v___x_617_, 4);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_617_, 1);
lean_dec(v_unused_660_);
v___x_623_ = v___x_617_;
v_isShared_624_ = v_isSharedCheck_659_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_diag_621_);
lean_inc(v_postponed_620_);
lean_inc(v_zetaDeltaFVarIds_619_);
lean_inc(v_mctx_618_);
lean_dec(v___x_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_659_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_mctx_618_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_zetaDeltaFVarIds_619_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_postponed_620_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_diag_621_);
v___x_627_ = v_reuseFailAlloc_658_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v_r_629_; 
v___x_628_ = lean_st_ref_put(v___y_589_, v___x_627_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
v_r_629_ = lean_apply_5(v_x_586_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, lean_box(0));
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_646_; 
v_a_630_ = lean_ctor_get(v_r_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_r_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_632_ = v_r_629_;
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v_r_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_646_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
lean_inc(v_a_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_645_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v___x_636_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_591_, v_isExporting_598_, v___x_613_, v___y_589_, v___x_625_, v___x_635_);
lean_dec_ref(v___x_635_);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_636_, 0);
lean_dec(v_unused_644_);
v___x_638_ = v___x_636_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_dec(v___x_636_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_a_630_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_630_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_647_ = lean_ctor_get(v_r_629_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v_r_629_, 1);
v___x_648_ = lean_box(0);
v___x_649_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_591_, v_isExporting_598_, v___x_613_, v___y_589_, v___x_625_, v___x_648_);
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
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 0, v_a_647_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_647_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_666_, lean_object* v_isExporting_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v_isExporting_boxed_673_; lean_object* v_res_674_; 
v_isExporting_boxed_673_ = lean_unbox(v_isExporting_667_);
v_res_674_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_666_, v_isExporting_boxed_673_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object* v_x_675_, uint8_t v_when_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
if (v_when_676_ == 0)
{
lean_object* v___x_682_; 
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
v___x_682_ = lean_apply_5(v_x_675_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, lean_box(0));
return v___x_682_;
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; 
v___x_683_ = 0;
v___x_684_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_675_, v___x_683_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object* v_x_685_, lean_object* v_when_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_when_boxed_692_; lean_object* v_res_693_; 
v_when_boxed_692_ = lean_unbox(v_when_686_);
v_res_693_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_685_, v_when_boxed_692_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_693_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__0));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__2));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__4));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__5, &l_Lean_validateDefEqAttr___lam__0___closed__5_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__5);
v___x_704_ = l_Lean_MessageData_note(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* v_lhs_705_, lean_object* v_rhs_706_, uint8_t v___x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_lhs_705_, v_rhs_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_763_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_763_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_763_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_763_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_762_; 
v_fst_718_ = lean_ctor_get(v_a_714_, 0);
v_snd_719_ = lean_ctor_get(v_a_714_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_762_ == 0)
{
v___x_721_ = v_a_714_;
v_isShared_722_ = v_isSharedCheck_762_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_inc(v_fst_718_);
lean_dec(v_a_714_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_762_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v_env_724_; uint8_t v_isExporting_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_723_ = lean_st_ref_get(v___y_711_);
v_env_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc_ref(v_env_724_);
lean_dec(v___x_723_);
v_isExporting_725_ = lean_ctor_get_uint8(v_env_724_, sizeof(void*)*8);
lean_dec_ref(v_env_724_);
v___x_726_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__1, &l_Lean_validateDefEqAttr___lam__0___closed__1_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__1);
lean_inc(v_fst_718_);
v___x_727_ = l_Lean_indentExpr(v_fst_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 7);
lean_ctor_set(v___x_721_, 1, v___x_727_);
lean_ctor_set(v___x_721_, 0, v___x_726_);
v___x_729_ = v___x_721_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_761_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__3, &l_Lean_validateDefEqAttr___lam__0___closed__3_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__3);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc(v_snd_719_);
v___x_732_ = l_Lean_indentExpr(v_snd_719_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
if (v_isExporting_725_ == 0)
{
lean_object* v___x_735_; 
lean_dec(v_snd_719_);
lean_dec(v_fst_718_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_733_);
v___x_735_ = v___x_716_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_716_);
v___x_737_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed), 7, 2);
lean_closure_set(v___x_737_, 0, v_fst_718_);
lean_closure_set(v___x_737_, 1, v_snd_719_);
v___x_738_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___x_737_, v___x_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_752_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_752_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_752_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_752_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_743_; 
v___x_743_ = lean_unbox(v_a_739_);
lean_dec(v_a_739_);
if (v___x_743_ == 0)
{
lean_object* v___x_745_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_733_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_733_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__6, &l_Lean_validateDefEqAttr___lam__0___closed__6_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__6);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_733_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_748_);
v___x_750_ = v___x_741_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref_known(v___x_733_, 2);
v_a_753_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_738_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_738_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
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
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_a_764_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_713_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_713_);
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
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object* v_lhs_772_, lean_object* v_rhs_773_, lean_object* v___x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_6391__boxed_780_; lean_object* v_res_781_; 
v___x_6391__boxed_780_ = lean_unbox(v___x_774_);
v_res_781_ = l_Lean_validateDefEqAttr___lam__0(v_lhs_772_, v_rhs_773_, v___x_6391__boxed_780_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* v_lhs_782_, lean_object* v_rhs_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; 
lean_inc_ref(v_rhs_783_);
lean_inc_ref(v_lhs_782_);
v___x_789_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_lhs_782_, v_rhs_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_808_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_808_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint8_t v___x_794_; 
v___x_794_ = lean_unbox(v_a_790_);
lean_dec(v_a_790_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_792_);
v___x_795_ = 1;
v___x_796_ = lean_box(v___x_795_);
lean_inc_ref(v_rhs_783_);
lean_inc_ref(v_lhs_782_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_797_, 0, v_lhs_782_);
lean_closure_set(v___f_797_, 1, v_rhs_783_);
lean_closure_set(v___f_797_, 2, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(2u);
v___x_799_ = lean_mk_empty_array_with_capacity(v___x_798_);
v___x_800_ = lean_array_push(v___x_799_, v_lhs_782_);
v___x_801_ = lean_array_push(v___x_800_, v_rhs_783_);
v___x_802_ = l_Lean_MessageData_ofLazyM(v___f_797_, v___x_801_);
v___x_803_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_802_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec_ref(v_rhs_783_);
lean_dec_ref(v_lhs_782_);
v___x_804_ = lean_box(0);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_804_);
v___x_806_ = v___x_792_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_rhs_783_);
lean_dec_ref(v_lhs_782_);
v_a_809_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_789_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_789_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* v_lhs_817_, lean_object* v_rhs_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_817_, v_rhs_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_ctor_set(v___x_830_, 4, v___x_828_);
lean_ctor_set(v___x_830_, 5, v___x_828_);
lean_ctor_set(v___x_830_, 6, v___x_828_);
lean_ctor_set(v___x_830_, 7, v___x_828_);
lean_ctor_set(v___x_830_, 8, v___x_828_);
lean_ctor_set(v___x_830_, 9, v___x_828_);
lean_ctor_set(v___x_830_, 10, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(32u);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((size_t)5ULL);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_unsigned_to_nat(32u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_839_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
lean_ctor_set(v___x_839_, 2, v___x_835_);
lean_ctor_set(v___x_839_, 3, v___x_835_);
lean_ctor_set_usize(v___x_839_, 4, v___x_834_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = lean_box(1);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v___x_841_);
lean_ctor_set(v___x_843_, 2, v___x_840_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v_env_870_; uint8_t v___x_871_; 
v___x_869_ = lean_st_ref_get(v___y_867_);
v_env_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_env_870_);
lean_dec(v___x_869_);
v___x_871_ = l_Lean_Name_isAnonymous(v_declHint_866_);
if (v___x_871_ == 0)
{
uint8_t v_isExporting_872_; 
v_isExporting_872_ = lean_ctor_get_uint8(v_env_870_, sizeof(void*)*8);
if (v_isExporting_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_msg_865_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; uint8_t v___x_875_; 
lean_inc_ref(v_env_870_);
v___x_874_ = l_Lean_Environment_setExporting(v_env_870_, v___x_871_);
lean_inc(v_declHint_866_);
lean_inc_ref(v___x_874_);
v___x_875_ = l_Lean_Environment_contains(v___x_874_, v_declHint_866_, v_isExporting_872_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_msg_865_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_c_882_; lean_object* v___x_883_; 
v___x_877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_879_ = l_Lean_Options_empty;
v___x_880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_880_, 0, v___x_874_);
lean_ctor_set(v___x_880_, 1, v___x_877_);
lean_ctor_set(v___x_880_, 2, v___x_878_);
lean_ctor_set(v___x_880_, 3, v___x_879_);
lean_inc(v_declHint_866_);
v___x_881_ = l_Lean_MessageData_ofConstName(v_declHint_866_, v___x_871_);
v_c_882_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_882_, 0, v___x_880_);
lean_ctor_set(v_c_882_, 1, v___x_881_);
v___x_883_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_870_, v_declHint_866_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_c_882_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_note(v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v_msg_865_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
else
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_926_; 
v_val_891_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_926_ == 0)
{
v___x_893_ = v___x_883_;
v_isShared_894_ = v_isSharedCheck_926_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v___x_883_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_926_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_mod_898_; uint8_t v___x_899_; 
v___x_895_ = lean_box(0);
v___x_896_ = l_Lean_Environment_header(v_env_870_);
lean_dec_ref(v_env_870_);
v___x_897_ = l_Lean_EnvironmentHeader_moduleNames(v___x_896_);
v_mod_898_ = lean_array_get(v___x_895_, v___x_897_, v_val_891_);
lean_dec(v_val_891_);
lean_dec_ref(v___x_897_);
v___x_899_ = l_Lean_isPrivateName(v_declHint_866_);
lean_dec(v_declHint_866_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_c_882_);
v___x_902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_MessageData_ofName(v_mod_898_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_MessageData_note(v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v_msg_865_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___x_909_);
v___x_911_ = v___x_893_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_c_882_);
v___x_915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_MessageData_ofName(v_mod_898_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_MessageData_note(v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v_msg_865_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 0);
lean_ctor_set(v___x_893_, 0, v___x_922_);
v___x_924_ = v___x_893_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v_env_870_);
lean_dec(v_declHint_866_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msg_865_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_928_, lean_object* v_declHint_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_928_, v_declHint_929_, v___y_930_);
lean_dec(v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_933_, lean_object* v_declHint_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v___x_938_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_933_, v_declHint_934_, v___y_936_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = l_Lean_unknownIdentifierMessageTag;
v___x_944_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_949_, lean_object* v_declHint_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_949_, v_declHint_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_env_960_; lean_object* v_options_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
v_options_961_ = lean_ctor_get(v___y_956_, 1);
v___x_962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_963_ = lean_unsigned_to_nat(32u);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
lean_dec_ref(v___x_964_);
v___x_965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_961_);
v___x_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_966_, 0, v_env_960_);
lean_ctor_set(v___x_966_, 1, v___x_962_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
lean_ctor_set(v___x_966_, 3, v_options_961_);
v___x_967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_msgData_955_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_ref_978_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
v_ref_978_ = lean_ctor_get(v___y_975_, 4);
v___x_979_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_974_, v___y_975_, v___y_976_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_988_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_inc(v_ref_978_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_ref_978_);
lean_ctor_set(v___x_984_, 1, v_a_980_);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 1);
lean_ctor_set(v___x_982_, 0, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_994_, lean_object* v_msg_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_toCold_999_; lean_object* v_options_1000_; lean_object* v_currRecDepth_1001_; lean_object* v_maxRecDepth_1002_; lean_object* v_ref_1003_; lean_object* v_currNamespace_1004_; lean_object* v_openDecls_1005_; lean_object* v_initHeartbeats_1006_; lean_object* v_maxHeartbeats_1007_; lean_object* v_currMacroScope_1008_; uint8_t v_diag_1009_; uint8_t v_suppressElabErrors_1010_; lean_object* v_ref_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_toCold_999_ = lean_ctor_get(v___y_996_, 0);
v_options_1000_ = lean_ctor_get(v___y_996_, 1);
v_currRecDepth_1001_ = lean_ctor_get(v___y_996_, 2);
v_maxRecDepth_1002_ = lean_ctor_get(v___y_996_, 3);
v_ref_1003_ = lean_ctor_get(v___y_996_, 4);
v_currNamespace_1004_ = lean_ctor_get(v___y_996_, 5);
v_openDecls_1005_ = lean_ctor_get(v___y_996_, 6);
v_initHeartbeats_1006_ = lean_ctor_get(v___y_996_, 7);
v_maxHeartbeats_1007_ = lean_ctor_get(v___y_996_, 8);
v_currMacroScope_1008_ = lean_ctor_get(v___y_996_, 9);
v_diag_1009_ = lean_ctor_get_uint8(v___y_996_, sizeof(void*)*10);
v_suppressElabErrors_1010_ = lean_ctor_get_uint8(v___y_996_, sizeof(void*)*10 + 1);
v_ref_1011_ = l_Lean_replaceRef(v_ref_994_, v_ref_1003_);
lean_inc(v_currMacroScope_1008_);
lean_inc(v_maxHeartbeats_1007_);
lean_inc(v_initHeartbeats_1006_);
lean_inc(v_openDecls_1005_);
lean_inc(v_currNamespace_1004_);
lean_inc(v_maxRecDepth_1002_);
lean_inc(v_currRecDepth_1001_);
lean_inc_ref(v_options_1000_);
lean_inc_ref(v_toCold_999_);
v___x_1012_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1012_, 0, v_toCold_999_);
lean_ctor_set(v___x_1012_, 1, v_options_1000_);
lean_ctor_set(v___x_1012_, 2, v_currRecDepth_1001_);
lean_ctor_set(v___x_1012_, 3, v_maxRecDepth_1002_);
lean_ctor_set(v___x_1012_, 4, v_ref_1011_);
lean_ctor_set(v___x_1012_, 5, v_currNamespace_1004_);
lean_ctor_set(v___x_1012_, 6, v_openDecls_1005_);
lean_ctor_set(v___x_1012_, 7, v_initHeartbeats_1006_);
lean_ctor_set(v___x_1012_, 8, v_maxHeartbeats_1007_);
lean_ctor_set(v___x_1012_, 9, v_currMacroScope_1008_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*10, v_diag_1009_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*10 + 1, v_suppressElabErrors_1010_);
v___x_1013_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_995_, v___x_1012_, v___y_997_);
lean_dec_ref_known(v___x_1012_, 10);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1014_, lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1014_, v_msg_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v_ref_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1020_, lean_object* v_msg_1021_, lean_object* v_declHint_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1021_, v_declHint_1022_, v___y_1023_, v___y_1024_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1020_, v_a_1027_, v___y_1023_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1029_, lean_object* v_msg_1030_, lean_object* v_declHint_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1029_, v_msg_1030_, v_declHint_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_ref_1029_);
return v_res_1035_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1042_, lean_object* v_constName_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1047_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1048_ = 0;
lean_inc(v_constName_1043_);
v___x_1049_ = l_Lean_MessageData_ofConstName(v_constName_1043_, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1042_, v___x_1052_, v_constName_1043_, v___y_1044_, v___y_1045_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1054_, lean_object* v_constName_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1054_, v_constName_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v_ref_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object* v_constName_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_ref_1064_; lean_object* v___x_1065_; 
v_ref_1064_ = lean_ctor_get(v___y_1061_, 4);
v___x_1065_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1064_, v_constName_1060_, v___y_1061_, v___y_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object* v_constName_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_env_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_st_ref_get(v___y_1073_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = 0;
lean_inc(v_constName_1071_);
v___x_1078_ = l_Lean_Environment_findConstVal_x3f(v_env_1076_, v_constName_1071_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1071_, v___y_1072_, v___y_1073_);
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_constName_1071_);
v_val_1080_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_val_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object* v_constName_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1092_;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__1(void){
_start:
{
lean_object* v___x_1099_; uint64_t v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__2(void){
_start:
{
uint64_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_uint64_once(&l_Lean_validateDefEqAttr___closed__1, &l_Lean_validateDefEqAttr___closed__1_once, _init_l_Lean_validateDefEqAttr___closed__1);
v___x_1102_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1103_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set_uint64(v___x_1103_, sizeof(void*)*1, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3(void){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__3, &l_Lean_validateDefEqAttr___closed__3_once, _init_l_Lean_validateDefEqAttr___closed__3);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_box(1);
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1109_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
lean_ctor_set(v___x_1110_, 2, v___x_1107_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7(void){
_start:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1113_ = 1;
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_box(0);
v___x_1116_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__6));
v___x_1117_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__5, &l_Lean_validateDefEqAttr___closed__5_once, _init_l_Lean_validateDefEqAttr___closed__5);
v___x_1118_ = lean_box(1);
v___x_1119_ = 0;
v___x_1120_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__2, &l_Lean_validateDefEqAttr___closed__2_once, _init_l_Lean_validateDefEqAttr___closed__2);
v___x_1121_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___x_1118_);
lean_ctor_set(v___x_1121_, 2, v___x_1117_);
lean_ctor_set(v___x_1121_, 3, v___x_1116_);
lean_ctor_set(v___x_1121_, 4, v___x_1115_);
lean_ctor_set(v___x_1121_, 5, v___x_1114_);
lean_ctor_set(v___x_1121_, 6, v___x_1115_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*7, v___x_1119_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*7 + 1, v___x_1119_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*7 + 2, v___x_1119_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*7 + 3, v___x_1113_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_ctor_set(v___x_1124_, 2, v___x_1123_);
lean_ctor_set(v___x_1124_, 3, v___x_1123_);
lean_ctor_set(v___x_1124_, 4, v___x_1122_);
lean_ctor_set(v___x_1124_, 5, v___x_1122_);
lean_ctor_set(v___x_1124_, 6, v___x_1122_);
lean_ctor_set(v___x_1124_, 7, v___x_1122_);
lean_ctor_set(v___x_1124_, 8, v___x_1122_);
lean_ctor_set(v___x_1124_, 9, v___x_1122_);
lean_ctor_set(v___x_1124_, 10, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1126_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_ctor_set(v___x_1126_, 2, v___x_1125_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
lean_ctor_set(v___x_1126_, 4, v___x_1125_);
lean_ctor_set(v___x_1126_, 5, v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
lean_ctor_set(v___x_1128_, 2, v___x_1127_);
lean_ctor_set(v___x_1128_, 3, v___x_1127_);
lean_ctor_set(v___x_1128_, 4, v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1129_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__10, &l_Lean_validateDefEqAttr___closed__10_once, _init_l_Lean_validateDefEqAttr___closed__10);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1131_ = lean_box(1);
v___x_1132_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__9, &l_Lean_validateDefEqAttr___closed__9_once, _init_l_Lean_validateDefEqAttr___closed__9);
v___x_1133_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__8, &l_Lean_validateDefEqAttr___closed__8_once, _init_l_Lean_validateDefEqAttr___closed__8);
v___x_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
lean_ctor_set(v___x_1134_, 2, v___x_1131_);
lean_ctor_set(v___x_1134_, 3, v___x_1130_);
lean_ctor_set(v___x_1134_, 4, v___x_1129_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object* v_declName_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_declName_1136_, v_a_1137_, v_a_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_type_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__7, &l_Lean_validateDefEqAttr___closed__7_once, _init_l_Lean_validateDefEqAttr___closed__7);
v___x_1143_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__11, &l_Lean_validateDefEqAttr___closed__11_once, _init_l_Lean_validateDefEqAttr___closed__11);
v___x_1144_ = lean_st_mk_ref(v___x_1143_);
v_type_1145_ = lean_ctor_get(v_a_1141_, 2);
lean_inc_ref(v_type_1145_);
lean_dec(v_a_1141_);
v___f_1146_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__12));
v___x_1147_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_1145_, v___f_1146_, v___x_1142_, v___x_1144_, v_a_1137_, v_a_1138_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_st_ref_get(v___x_1144_);
lean_dec(v___x_1144_);
lean_dec(v___x_1152_);
if (v_isShared_1151_ == 0)
{
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1148_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_dec(v___x_1144_);
return v___x_1147_;
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1140_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1140_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object* v_declName_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_validateDefEqAttr(v_declName_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_1170_, lean_object* v_x_1171_, uint8_t v_isExporting_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_1171_, v_isExporting_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_x_1180_, lean_object* v_isExporting_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_isExporting_boxed_1187_; lean_object* v_res_1188_; 
v_isExporting_boxed_1187_ = lean_unbox(v_isExporting_1181_);
v_res_1188_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_1179_, v_x_1180_, v_isExporting_boxed_1187_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object* v_00_u03b1_1189_, lean_object* v_x_1190_, uint8_t v_when_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_1190_, v_when_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_x_1199_, lean_object* v_when_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_when_boxed_1206_; lean_object* v_res_1207_; 
v_when_boxed_1206_ = lean_unbox(v_when_1200_);
v_res_1207_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(v_00_u03b1_1198_, v_x_1199_, v_when_boxed_1206_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object* v_00_u03b1_1208_, lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_constName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_1214_, v_constName_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1220_, lean_object* v_ref_1221_, lean_object* v_constName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1221_, v_constName_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_ref_1228_, lean_object* v_constName_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_1227_, v_ref_1228_, v_constName_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v_ref_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1234_, lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_ref_1243_, lean_object* v_msg_1244_, lean_object* v_declHint_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1242_, v_ref_1243_, v_msg_1244_, v_declHint_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v_ref_1243_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1250_, lean_object* v_declHint_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1250_, v_declHint_1251_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1256_, lean_object* v_declHint_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1256_, v_declHint_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1262_, lean_object* v_ref_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1263_, v_msg_1264_, v___y_1265_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_ref_1270_, lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1269_, v_ref_1270_, v_msg_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v_ref_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1282_, v_msg_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1301_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1302_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1303_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1304_ = 0;
v___x_1305_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1306_ = l_Lean_registerTagAttribute(v___x_1300_, v___x_1301_, v___x_1302_, v___x_1303_, v___x_1304_, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1(){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1312_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0));
v___x_1313_ = l_Lean_addBuiltinDocString(v___x_1311_, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1343_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6));
v___x_1344_ = l_Lean_addBuiltinDeclarationRanges(v___x_1342_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
return v_res_1346_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_attrName_1359_, lean_object* v_declName_1360_, lean_object* v_asyncPrefix_x3f_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___y_1366_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1361_) == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_MessageData_nil;
v___y_1366_ = v___x_1379_;
goto v___jp_1365_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_val_1380_ = lean_ctor_get(v_asyncPrefix_x3f_1361_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_asyncPrefix_x3f_1361_, 1);
v___x_1381_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1382_ = l_Lean_MessageData_ofName(v_val_1380_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___y_1366_ = v___x_1385_;
goto v___jp_1365_;
}
v___jp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1367_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1368_ = l_Lean_MessageData_ofName(v_attrName_1359_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = 0;
v___x_1373_ = l_Lean_MessageData_ofConstName(v_declName_1360_, v___x_1372_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1371_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___y_1366_);
v___x_1378_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1377_, v___y_1362_, v___y_1363_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1386_, lean_object* v_declName_1387_, lean_object* v_asyncPrefix_x3f_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1386_, v_declName_1387_, v_asyncPrefix_x3f_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1392_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_attrName_1396_, lean_object* v_declName_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1401_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1402_ = l_Lean_MessageData_ofName(v_attrName_1396_);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = 0;
v___x_1407_ = l_Lean_MessageData_ofConstName(v_declName_1397_, v___x_1406_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1405_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1410_, v___y_1398_, v___y_1399_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1412_, lean_object* v_declName_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1412_, v_declName_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object* v_attr_1418_, lean_object* v_decl_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___y_1424_; lean_object* v___x_1450_; lean_object* v_env_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___x_1464_; 
v___x_1450_ = lean_st_ref_get(v___y_1421_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1464_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1451_, v_decl_1419_);
if (lean_obj_tag(v___x_1464_) == 0)
{
v___y_1453_ = v___y_1420_;
v___y_1454_ = v___y_1421_;
goto v___jp_1452_;
}
else
{
lean_object* v_attr_1465_; lean_object* v_toAttributeImplCore_1466_; lean_object* v_name_1467_; lean_object* v___x_1468_; 
lean_dec_ref_known(v___x_1464_, 1);
lean_dec_ref(v_env_1451_);
v_attr_1465_ = lean_ctor_get(v_attr_1418_, 0);
lean_inc_ref(v_attr_1465_);
lean_dec_ref(v_attr_1418_);
v_toAttributeImplCore_1466_ = lean_ctor_get(v_attr_1465_, 0);
lean_inc_ref(v_toAttributeImplCore_1466_);
lean_dec_ref(v_attr_1465_);
v_name_1467_ = lean_ctor_get(v_toAttributeImplCore_1466_, 1);
lean_inc(v_name_1467_);
lean_dec_ref(v_toAttributeImplCore_1466_);
v___x_1468_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_1467_, v_decl_1419_, v___y_1420_, v___y_1421_);
return v___x_1468_;
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v_ext_1426_; lean_object* v_toEnvExtension_1427_; lean_object* v_env_1428_; lean_object* v_nextMacroScope_1429_; lean_object* v_ngen_1430_; lean_object* v_auxDeclNGen_1431_; lean_object* v_traceState_1432_; lean_object* v_messages_1433_; lean_object* v_infoState_1434_; lean_object* v_snapshotTasks_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1448_; 
v___x_1425_ = lean_st_ref_take(v___y_1424_);
v_ext_1426_ = lean_ctor_get(v_attr_1418_, 1);
lean_inc_ref(v_ext_1426_);
lean_dec_ref(v_attr_1418_);
v_toEnvExtension_1427_ = lean_ctor_get(v_ext_1426_, 0);
v_env_1428_ = lean_ctor_get(v___x_1425_, 0);
v_nextMacroScope_1429_ = lean_ctor_get(v___x_1425_, 1);
v_ngen_1430_ = lean_ctor_get(v___x_1425_, 2);
v_auxDeclNGen_1431_ = lean_ctor_get(v___x_1425_, 3);
v_traceState_1432_ = lean_ctor_get(v___x_1425_, 4);
v_messages_1433_ = lean_ctor_get(v___x_1425_, 6);
v_infoState_1434_ = lean_ctor_get(v___x_1425_, 7);
v_snapshotTasks_1435_ = lean_ctor_get(v___x_1425_, 8);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1425_, 5);
lean_dec(v_unused_1449_);
v___x_1437_ = v___x_1425_;
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snapshotTasks_1435_);
lean_inc(v_infoState_1434_);
lean_inc(v_messages_1433_);
lean_inc(v_traceState_1432_);
lean_inc(v_auxDeclNGen_1431_);
lean_inc(v_ngen_1430_);
lean_inc(v_nextMacroScope_1429_);
lean_inc(v_env_1428_);
lean_dec(v___x_1425_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_asyncMode_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v_asyncMode_1439_ = lean_ctor_get(v_toEnvExtension_1427_, 2);
lean_inc(v_asyncMode_1439_);
lean_inc(v_decl_1419_);
v___x_1440_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1426_, v_env_1428_, v_decl_1419_, v_asyncMode_1439_, v_decl_1419_);
lean_dec(v_asyncMode_1439_);
v___x_1441_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 5, v___x_1441_);
lean_ctor_set(v___x_1437_, 0, v___x_1440_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_nextMacroScope_1429_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_ngen_1430_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_auxDeclNGen_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_traceState_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_messages_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_infoState_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_snapshotTasks_1435_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_st_ref_put(v___y_1424_, v___x_1443_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
v___jp_1452_:
{
lean_object* v_ext_1455_; lean_object* v_toEnvExtension_1456_; lean_object* v_attr_1457_; lean_object* v_asyncMode_1458_; uint8_t v___x_1459_; 
v_ext_1455_ = lean_ctor_get(v_attr_1418_, 1);
v_toEnvExtension_1456_ = lean_ctor_get(v_ext_1455_, 0);
v_attr_1457_ = lean_ctor_get(v_attr_1418_, 0);
v_asyncMode_1458_ = lean_ctor_get(v_toEnvExtension_1456_, 2);
lean_inc(v_decl_1419_);
lean_inc_ref(v_env_1451_);
v___x_1459_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1451_, v_decl_1419_, v_asyncMode_1458_);
if (v___x_1459_ == 0)
{
lean_object* v_toAttributeImplCore_1460_; lean_object* v_name_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc_ref(v_attr_1457_);
lean_dec_ref(v_attr_1418_);
v_toAttributeImplCore_1460_ = lean_ctor_get(v_attr_1457_, 0);
lean_inc_ref(v_toAttributeImplCore_1460_);
lean_dec_ref(v_attr_1457_);
v_name_1461_ = lean_ctor_get(v_toAttributeImplCore_1460_, 1);
lean_inc(v_name_1461_);
lean_dec_ref(v_toAttributeImplCore_1460_);
v___x_1462_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1451_);
v___x_1463_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_1461_, v_decl_1419_, v___x_1462_, v___y_1453_, v___y_1454_);
return v___x_1463_;
}
else
{
lean_dec_ref(v_env_1451_);
v___y_1424_ = v___y_1454_;
goto v___jp_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object* v_attr_1469_, lean_object* v_decl_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1469_, v_decl_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object* v_declName_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
lean_inc(v_declName_1475_);
v___x_1479_ = l_Lean_validateDefEqAttr(v_declName_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref_known(v___x_1479_, 1);
v___x_1480_ = l_Lean_backwardDefeqAttr;
v___x_1481_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v___x_1480_, v_declName_1475_, v___y_1476_, v___y_1477_);
return v___x_1481_;
}
else
{
lean_dec(v_declName_1475_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_declName_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___f_1497_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1498_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1499_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1500_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1501_ = 0;
v___x_1502_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1503_ = l_Lean_registerTagAttribute(v___x_1498_, v___x_1499_, v___f_1497_, v___x_1500_, v___x_1501_, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1506_, lean_object* v_attrName_1507_, lean_object* v_declName_1508_, lean_object* v_asyncPrefix_x3f_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1507_, v_declName_1508_, v_asyncPrefix_x3f_1509_, v___y_1510_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1514_, lean_object* v_attrName_1515_, lean_object* v_declName_1516_, lean_object* v_asyncPrefix_x3f_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1514_, v_attrName_1515_, v_declName_1516_, v_asyncPrefix_x3f_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_1522_, lean_object* v_attrName_1523_, lean_object* v_declName_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1523_, v_declName_1524_, v___y_1525_, v___y_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_attrName_1530_, lean_object* v_declName_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_1529_, v_attrName_1530_, v_declName_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1539_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0));
v___x_1540_ = l_Lean_addBuiltinDocString(v___x_1538_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1570_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6));
v___x_1571_ = l_Lean_addBuiltinDeclarationRanges(v___x_1569_, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* v_type_1585_, lean_object* v_proof_1586_, lean_object* v_a_1587_){
_start:
{
if (lean_obj_tag(v_type_1585_) == 7)
{
if (lean_obj_tag(v_proof_1586_) == 6)
{
lean_object* v_body_1589_; lean_object* v_body_1590_; 
v_body_1589_ = lean_ctor_get(v_type_1585_, 2);
v_body_1590_ = lean_ctor_get(v_proof_1586_, 2);
lean_inc_ref(v_body_1590_);
lean_dec_ref_known(v_proof_1586_, 3);
v_type_1585_ = v_body_1589_;
v_proof_1586_ = v_body_1590_;
goto _start;
}
else
{
uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref(v_proof_1586_);
v___x_1592_ = 0;
v___x_1593_ = lean_box(v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_1596_ = lean_unsigned_to_nat(3u);
v___x_1597_ = l_Lean_Expr_isAppOfArity(v_type_1585_, v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v_proof_1586_);
v___x_1598_ = lean_box(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1));
v___x_1601_ = lean_unsigned_to_nat(2u);
v___x_1602_ = l_Lean_Expr_isAppOfArity(v_proof_1586_, v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3));
v___x_1604_ = l_Lean_Expr_isAppOfArity(v_proof_1586_, v___x_1603_, v___x_1601_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5));
v___x_1606_ = lean_unsigned_to_nat(4u);
v___x_1607_ = l_Lean_Expr_isAppOfArity(v_proof_1586_, v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = l_Lean_Expr_getAppFn(v_proof_1586_);
lean_dec_ref(v_proof_1586_);
v___x_1609_ = l_Lean_Expr_isConst(v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v___x_1608_);
v___x_1610_ = lean_box(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v_env_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1612_ = lean_st_ref_get(v_a_1587_);
v_env_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc_ref_n(v_env_1613_, 2);
lean_dec(v___x_1612_);
v___x_1614_ = l_Lean_Expr_constName_x21(v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1615_ = l_Lean_defeqAttr;
lean_inc(v___x_1614_);
v___x_1616_ = l_Lean_TagAttribute_hasTag(v___x_1615_, v_env_1613_, v___x_1614_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = l_Lean_backwardDefeqAttr;
v___x_1618_ = l_Lean_TagAttribute_hasTag(v___x_1617_, v_env_1613_, v___x_1614_);
v___x_1619_ = lean_box(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v___x_1614_);
lean_dec_ref(v_env_1613_);
v___x_1621_ = lean_box(v___x_1597_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Expr_appArg_x21(v_proof_1586_);
lean_dec_ref(v_proof_1586_);
v_proof_1586_ = v___x_1623_;
goto _start;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec_ref(v_proof_1586_);
v___x_1625_ = lean_box(v___x_1597_);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec_ref(v_proof_1586_);
v___x_1627_ = lean_box(v___x_1597_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* v_type_1629_, lean_object* v_proof_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1629_, v_proof_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_type_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* v_type_1634_, lean_object* v_proof_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1634_, v_proof_1635_, v_a_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* v_type_1640_, lean_object* v_proof_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1640_, v_proof_1641_, v_a_1642_, v_a_1643_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec_ref(v_type_1640_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object* v_attrName_1646_, lean_object* v_declName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1653_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1654_ = l_Lean_MessageData_ofName(v_attrName_1646_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = 0;
v___x_1659_ = l_Lean_MessageData_ofConstName(v_declName_1647_, v___x_1658_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1657_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1662_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1664_, lean_object* v_declName_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1664_, v_declName_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object* v_attrName_1672_, lean_object* v_declName_1673_, lean_object* v_asyncPrefix_x3f_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___y_1681_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1674_) == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_MessageData_nil;
v___y_1681_ = v___x_1694_;
goto v___jp_1680_;
}
else
{
lean_object* v_val_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1695_ = lean_ctor_get(v_asyncPrefix_x3f_1674_, 0);
lean_inc(v_val_1695_);
lean_dec_ref_known(v_asyncPrefix_x3f_1674_, 1);
v___x_1696_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1697_ = l_Lean_MessageData_ofName(v_val_1695_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___y_1681_ = v___x_1700_;
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1682_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1683_ = l_Lean_MessageData_ofName(v_attrName_1672_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = 0;
v___x_1688_ = l_Lean_MessageData_ofConstName(v_declName_1673_, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1686_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___y_1681_);
v___x_1693_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1692_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1701_, lean_object* v_declName_1702_, lean_object* v_asyncPrefix_x3f_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1701_, v_declName_1702_, v_asyncPrefix_x3f_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object* v_attr_1710_, lean_object* v_decl_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1760_; lean_object* v_env_1761_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1776_; 
v___x_1760_ = lean_st_ref_get(v___y_1715_);
v_env_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_env_1761_);
lean_dec(v___x_1760_);
v___x_1776_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1761_, v_decl_1711_);
if (lean_obj_tag(v___x_1776_) == 0)
{
v___y_1763_ = v___y_1712_;
v___y_1764_ = v___y_1713_;
v___y_1765_ = v___y_1714_;
v___y_1766_ = v___y_1715_;
goto v___jp_1762_;
}
else
{
lean_object* v_attr_1777_; lean_object* v_toAttributeImplCore_1778_; lean_object* v_name_1779_; lean_object* v___x_1780_; 
lean_dec_ref_known(v___x_1776_, 1);
lean_dec_ref(v_env_1761_);
v_attr_1777_ = lean_ctor_get(v_attr_1710_, 0);
lean_inc_ref(v_attr_1777_);
lean_dec_ref(v_attr_1710_);
v_toAttributeImplCore_1778_ = lean_ctor_get(v_attr_1777_, 0);
lean_inc_ref(v_toAttributeImplCore_1778_);
lean_dec_ref(v_attr_1777_);
v_name_1779_ = lean_ctor_get(v_toAttributeImplCore_1778_, 1);
lean_inc(v_name_1779_);
lean_dec_ref(v_toAttributeImplCore_1778_);
v___x_1780_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_1779_, v_decl_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1780_;
}
v___jp_1717_:
{
lean_object* v___x_1720_; lean_object* v_ext_1721_; lean_object* v_toEnvExtension_1722_; lean_object* v_env_1723_; lean_object* v_nextMacroScope_1724_; lean_object* v_ngen_1725_; lean_object* v_auxDeclNGen_1726_; lean_object* v_traceState_1727_; lean_object* v_messages_1728_; lean_object* v_infoState_1729_; lean_object* v_snapshotTasks_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1758_; 
v___x_1720_ = lean_st_ref_take(v___y_1719_);
v_ext_1721_ = lean_ctor_get(v_attr_1710_, 1);
lean_inc_ref(v_ext_1721_);
lean_dec_ref(v_attr_1710_);
v_toEnvExtension_1722_ = lean_ctor_get(v_ext_1721_, 0);
v_env_1723_ = lean_ctor_get(v___x_1720_, 0);
v_nextMacroScope_1724_ = lean_ctor_get(v___x_1720_, 1);
v_ngen_1725_ = lean_ctor_get(v___x_1720_, 2);
v_auxDeclNGen_1726_ = lean_ctor_get(v___x_1720_, 3);
v_traceState_1727_ = lean_ctor_get(v___x_1720_, 4);
v_messages_1728_ = lean_ctor_get(v___x_1720_, 6);
v_infoState_1729_ = lean_ctor_get(v___x_1720_, 7);
v_snapshotTasks_1730_ = lean_ctor_get(v___x_1720_, 8);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v___x_1720_, 5);
lean_dec(v_unused_1759_);
v___x_1732_ = v___x_1720_;
v_isShared_1733_ = v_isSharedCheck_1758_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snapshotTasks_1730_);
lean_inc(v_infoState_1729_);
lean_inc(v_messages_1728_);
lean_inc(v_traceState_1727_);
lean_inc(v_auxDeclNGen_1726_);
lean_inc(v_ngen_1725_);
lean_inc(v_nextMacroScope_1724_);
lean_inc(v_env_1723_);
lean_dec(v___x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1758_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_asyncMode_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v_asyncMode_1734_ = lean_ctor_get(v_toEnvExtension_1722_, 2);
lean_inc(v_asyncMode_1734_);
lean_inc(v_decl_1711_);
v___x_1735_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1721_, v_env_1723_, v_decl_1711_, v_asyncMode_1734_, v_decl_1711_);
lean_dec(v_asyncMode_1734_);
v___x_1736_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 5, v___x_1736_);
lean_ctor_set(v___x_1732_, 0, v___x_1735_);
v___x_1738_ = v___x_1732_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_nextMacroScope_1724_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_ngen_1725_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_auxDeclNGen_1726_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_traceState_1727_);
lean_ctor_set(v_reuseFailAlloc_1757_, 5, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1757_, 6, v_messages_1728_);
lean_ctor_set(v_reuseFailAlloc_1757_, 7, v_infoState_1729_);
lean_ctor_set(v_reuseFailAlloc_1757_, 8, v_snapshotTasks_1730_);
v___x_1738_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_mctx_1741_; lean_object* v_zetaDeltaFVarIds_1742_; lean_object* v_postponed_1743_; lean_object* v_diag_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1755_; 
v___x_1739_ = lean_st_ref_put(v___y_1719_, v___x_1738_);
v___x_1740_ = lean_st_ref_take(v___y_1718_);
v_mctx_1741_ = lean_ctor_get(v___x_1740_, 0);
v_zetaDeltaFVarIds_1742_ = lean_ctor_get(v___x_1740_, 2);
v_postponed_1743_ = lean_ctor_get(v___x_1740_, 3);
v_diag_1744_ = lean_ctor_get(v___x_1740_, 4);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1740_, 1);
lean_dec(v_unused_1756_);
v___x_1746_ = v___x_1740_;
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_diag_1744_);
lean_inc(v_postponed_1743_);
lean_inc(v_zetaDeltaFVarIds_1742_);
lean_inc(v_mctx_1741_);
lean_dec(v___x_1740_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_mctx_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_zetaDeltaFVarIds_1742_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_postponed_1743_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_diag_1744_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_st_ref_put(v___y_1718_, v___x_1750_);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
}
}
v___jp_1762_:
{
lean_object* v_ext_1767_; lean_object* v_toEnvExtension_1768_; lean_object* v_attr_1769_; lean_object* v_asyncMode_1770_; uint8_t v___x_1771_; 
v_ext_1767_ = lean_ctor_get(v_attr_1710_, 1);
v_toEnvExtension_1768_ = lean_ctor_get(v_ext_1767_, 0);
v_attr_1769_ = lean_ctor_get(v_attr_1710_, 0);
v_asyncMode_1770_ = lean_ctor_get(v_toEnvExtension_1768_, 2);
lean_inc(v_decl_1711_);
lean_inc_ref(v_env_1761_);
v___x_1771_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1761_, v_decl_1711_, v_asyncMode_1770_);
if (v___x_1771_ == 0)
{
lean_object* v_toAttributeImplCore_1772_; lean_object* v_name_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc_ref(v_attr_1769_);
lean_dec_ref(v_attr_1710_);
v_toAttributeImplCore_1772_ = lean_ctor_get(v_attr_1769_, 0);
lean_inc_ref(v_toAttributeImplCore_1772_);
lean_dec_ref(v_attr_1769_);
v_name_1773_ = lean_ctor_get(v_toAttributeImplCore_1772_, 1);
lean_inc(v_name_1773_);
lean_dec_ref(v_toAttributeImplCore_1772_);
v___x_1774_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1761_);
v___x_1775_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_1773_, v_decl_1711_, v___x_1774_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1775_;
}
else
{
lean_dec_ref(v_env_1761_);
v___y_1718_ = v___y_1764_;
v___y_1719_ = v___y_1766_;
goto v___jp_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object* v_attr_1781_, lean_object* v_decl_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_1781_, v_decl_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_1789_, lean_object* v_declHint_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v_env_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_st_ref_get(v___y_1791_);
v_env_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc_ref(v_env_1794_);
lean_dec(v___x_1793_);
v___x_1795_ = l_Lean_Name_isAnonymous(v_declHint_1790_);
if (v___x_1795_ == 0)
{
uint8_t v_isExporting_1796_; 
v_isExporting_1796_ = lean_ctor_get_uint8(v_env_1794_, sizeof(void*)*8);
if (v_isExporting_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v_env_1794_);
lean_dec(v_declHint_1790_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_msg_1789_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_inc_ref(v_env_1794_);
v___x_1798_ = l_Lean_Environment_setExporting(v_env_1794_, v___x_1795_);
lean_inc(v_declHint_1790_);
lean_inc_ref(v___x_1798_);
v___x_1799_ = l_Lean_Environment_contains(v___x_1798_, v_declHint_1790_, v_isExporting_1796_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_env_1794_);
lean_dec(v_declHint_1790_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_msg_1789_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_c_1808_; lean_object* v___x_1809_; 
v___x_1801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1802_ = lean_unsigned_to_nat(32u);
v___x_1803_ = lean_mk_empty_array_with_capacity(v___x_1802_);
lean_dec_ref(v___x_1803_);
v___x_1804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1805_ = l_Lean_Options_empty;
v___x_1806_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1798_);
lean_ctor_set(v___x_1806_, 1, v___x_1801_);
lean_ctor_set(v___x_1806_, 2, v___x_1804_);
lean_ctor_set(v___x_1806_, 3, v___x_1805_);
lean_inc(v_declHint_1790_);
v___x_1807_ = l_Lean_MessageData_ofConstName(v_declHint_1790_, v___x_1795_);
v_c_1808_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1808_, 0, v___x_1806_);
lean_ctor_set(v_c_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1794_, v_declHint_1790_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v_env_1794_);
lean_dec(v_declHint_1790_);
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_c_1808_);
v___x_1812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_MessageData_note(v___x_1813_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_msg_1789_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v_val_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1852_; 
v_val_1817_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1819_ = v___x_1809_;
v_isShared_1820_ = v_isSharedCheck_1852_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_val_1817_);
lean_dec(v___x_1809_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1852_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_mod_1824_; uint8_t v___x_1825_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = l_Lean_Environment_header(v_env_1794_);
lean_dec_ref(v_env_1794_);
v___x_1823_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1822_);
v_mod_1824_ = lean_array_get(v___x_1821_, v___x_1823_, v_val_1817_);
lean_dec(v_val_1817_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = l_Lean_isPrivateName(v_declHint_1790_);
lean_dec(v_declHint_1790_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_c_1808_);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_ofName(v_mod_1824_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_MessageData_note(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_msg_1789_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1835_);
v___x_1837_ = v___x_1819_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v_c_1808_);
v___x_1841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_MessageData_ofName(v_mod_1824_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_MessageData_note(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_msg_1789_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1848_);
v___x_1850_ = v___x_1819_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1853_; 
lean_dec_ref(v_env_1794_);
lean_dec(v_declHint_1790_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_msg_1789_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1854_, lean_object* v_declHint_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1854_, v_declHint_1855_, v___y_1856_);
lean_dec(v___y_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object* v_msg_1859_, lean_object* v_declHint_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1876_; 
v___x_1866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_1859_, v_declHint_1860_, v___y_1864_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = l_Lean_unknownIdentifierMessageTag;
v___x_1872_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object* v_msg_1877_, lean_object* v_declHint_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1877_, v_declHint_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object* v_ref_1885_, lean_object* v_msg_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_toCold_1892_; lean_object* v_options_1893_; lean_object* v_currRecDepth_1894_; lean_object* v_maxRecDepth_1895_; lean_object* v_ref_1896_; lean_object* v_currNamespace_1897_; lean_object* v_openDecls_1898_; lean_object* v_initHeartbeats_1899_; lean_object* v_maxHeartbeats_1900_; lean_object* v_currMacroScope_1901_; uint8_t v_diag_1902_; uint8_t v_suppressElabErrors_1903_; lean_object* v_ref_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_toCold_1892_ = lean_ctor_get(v___y_1889_, 0);
v_options_1893_ = lean_ctor_get(v___y_1889_, 1);
v_currRecDepth_1894_ = lean_ctor_get(v___y_1889_, 2);
v_maxRecDepth_1895_ = lean_ctor_get(v___y_1889_, 3);
v_ref_1896_ = lean_ctor_get(v___y_1889_, 4);
v_currNamespace_1897_ = lean_ctor_get(v___y_1889_, 5);
v_openDecls_1898_ = lean_ctor_get(v___y_1889_, 6);
v_initHeartbeats_1899_ = lean_ctor_get(v___y_1889_, 7);
v_maxHeartbeats_1900_ = lean_ctor_get(v___y_1889_, 8);
v_currMacroScope_1901_ = lean_ctor_get(v___y_1889_, 9);
v_diag_1902_ = lean_ctor_get_uint8(v___y_1889_, sizeof(void*)*10);
v_suppressElabErrors_1903_ = lean_ctor_get_uint8(v___y_1889_, sizeof(void*)*10 + 1);
v_ref_1904_ = l_Lean_replaceRef(v_ref_1885_, v_ref_1896_);
lean_inc(v_currMacroScope_1901_);
lean_inc(v_maxHeartbeats_1900_);
lean_inc(v_initHeartbeats_1899_);
lean_inc(v_openDecls_1898_);
lean_inc(v_currNamespace_1897_);
lean_inc(v_maxRecDepth_1895_);
lean_inc(v_currRecDepth_1894_);
lean_inc_ref(v_options_1893_);
lean_inc_ref(v_toCold_1892_);
v___x_1905_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1905_, 0, v_toCold_1892_);
lean_ctor_set(v___x_1905_, 1, v_options_1893_);
lean_ctor_set(v___x_1905_, 2, v_currRecDepth_1894_);
lean_ctor_set(v___x_1905_, 3, v_maxRecDepth_1895_);
lean_ctor_set(v___x_1905_, 4, v_ref_1904_);
lean_ctor_set(v___x_1905_, 5, v_currNamespace_1897_);
lean_ctor_set(v___x_1905_, 6, v_openDecls_1898_);
lean_ctor_set(v___x_1905_, 7, v_initHeartbeats_1899_);
lean_ctor_set(v___x_1905_, 8, v_maxHeartbeats_1900_);
lean_ctor_set(v___x_1905_, 9, v_currMacroScope_1901_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*10, v_diag_1902_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*10 + 1, v_suppressElabErrors_1903_);
v___x_1906_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_1886_, v___y_1887_, v___y_1888_, v___x_1905_, v___y_1890_);
lean_dec_ref_known(v___x_1905_, 10);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_ref_1907_, lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1907_, v_msg_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v_ref_1907_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object* v_ref_1915_, lean_object* v_msg_1916_, lean_object* v_declHint_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___x_1925_; 
v___x_1923_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_1916_, v_declHint_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_1915_, v_a_1924_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1926_, lean_object* v_msg_1927_, lean_object* v_declHint_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1926_, v_msg_1927_, v_declHint_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v_ref_1926_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object* v_ref_1935_, lean_object* v_constName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1942_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1943_ = 0;
lean_inc(v_constName_1936_);
v___x_1944_ = l_Lean_MessageData_ofConstName(v_constName_1936_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1942_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_1935_, v___x_1947_, v_constName_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object* v_ref_1949_, lean_object* v_constName_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1949_, v_constName_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_ref_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object* v_constName_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_ref_1963_; lean_object* v___x_1964_; 
v_ref_1963_ = lean_ctor_get(v___y_1960_, 4);
v___x_1964_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_1963_, v_constName_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object* v_constName_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object* v_constName_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v_env_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_st_ref_get(v___y_1976_);
v_env_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc_ref(v_env_1979_);
lean_dec(v___x_1978_);
v___x_1980_ = 0;
lean_inc(v_constName_1972_);
v___x_1981_ = l_Lean_Environment_find_x3f(v_env_1979_, v_constName_1972_, v___x_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1982_;
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_constName_1972_);
v_val_1983_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 0);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_val_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object* v_constName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_2005_, uint8_t v___y_2006_, lean_object* v_x_2007_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 1)
{
lean_object* v_pre_2008_; 
v_pre_2008_ = lean_ctor_get(v_x_2007_, 0);
switch(lean_obj_tag(v_pre_2008_))
{
case 1:
{
lean_object* v_pre_2009_; 
v_pre_2009_ = lean_ctor_get(v_pre_2008_, 0);
switch(lean_obj_tag(v_pre_2009_))
{
case 0:
{
lean_object* v_str_2010_; lean_object* v_str_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_str_2010_ = lean_ctor_get(v_x_2007_, 1);
v_str_2011_ = lean_ctor_get(v_pre_2008_, 1);
v___x_2012_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0));
v___x_2013_ = lean_string_dec_eq(v_str_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1));
v___x_2015_ = lean_string_dec_eq(v_str_2011_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2));
v___x_2017_ = lean_string_dec_eq(v_str_2010_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v___x_2017_;
}
else
{
return v_suppressElabErrors_2005_;
}
}
}
else
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3));
v___x_2019_ = lean_string_dec_eq(v_str_2010_, v___x_2018_);
if (v___x_2019_ == 0)
{
return v___x_2019_;
}
else
{
return v_suppressElabErrors_2005_;
}
}
}
case 1:
{
lean_object* v_pre_2020_; 
v_pre_2020_ = lean_ctor_get(v_pre_2009_, 0);
if (lean_obj_tag(v_pre_2020_) == 0)
{
lean_object* v_str_2021_; lean_object* v_str_2022_; lean_object* v_str_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_str_2021_ = lean_ctor_get(v_x_2007_, 1);
v_str_2022_ = lean_ctor_get(v_pre_2008_, 1);
v_str_2023_ = lean_ctor_get(v_pre_2009_, 1);
v___x_2024_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4));
v___x_2025_ = lean_string_dec_eq(v_str_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5));
v___x_2027_ = lean_string_dec_eq(v_str_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6));
v___x_2029_ = lean_string_dec_eq(v_str_2021_, v___x_2028_);
if (v___x_2029_ == 0)
{
return v___x_2029_;
}
else
{
return v_suppressElabErrors_2005_;
}
}
}
}
else
{
return v___y_2006_;
}
}
default: 
{
return v___y_2006_;
}
}
}
case 0:
{
lean_object* v_str_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_str_2030_ = lean_ctor_get(v_x_2007_, 1);
v___x_2031_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0));
v___x_2032_ = lean_string_dec_eq(v_str_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
return v___x_2032_;
}
else
{
return v_suppressElabErrors_2005_;
}
}
default: 
{
return v___y_2006_;
}
}
}
else
{
return v___y_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_2033_, lean_object* v___y_2034_, lean_object* v_x_2035_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2036_; uint8_t v___y_8399__boxed_2037_; uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_suppressElabErrors_boxed_2036_ = lean_unbox(v_suppressElabErrors_2033_);
v___y_8399__boxed_2037_ = lean_unbox(v___y_2034_);
v_res_2038_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_2036_, v___y_8399__boxed_2037_, v_x_2035_);
lean_dec(v_x_2035_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object* v_ref_2041_, lean_object* v_msgData_2042_, uint8_t v_severity_2043_, uint8_t v_isSilent_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; uint8_t v___y_2116_; uint8_t v___y_2117_; uint8_t v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2128_; uint8_t v___x_2133_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; uint8_t v___y_2139_; uint8_t v___y_2140_; uint8_t v___y_2142_; uint8_t v___x_2156_; 
v___x_2133_ = 2;
v___x_2156_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2043_, v___x_2133_);
if (v___x_2156_ == 0)
{
v___y_2142_ = v___x_2156_;
goto v___jp_2141_;
}
else
{
uint8_t v___x_2157_; 
lean_inc_ref(v_msgData_2042_);
v___x_2157_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2042_);
v___y_2142_ = v___x_2157_;
goto v___jp_2141_;
}
v___jp_2050_:
{
lean_object* v___x_2060_; lean_object* v_currNamespace_2061_; lean_object* v_openDecls_2062_; lean_object* v_env_2063_; lean_object* v_nextMacroScope_2064_; lean_object* v_ngen_2065_; lean_object* v_auxDeclNGen_2066_; lean_object* v_traceState_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2085_; 
v___x_2060_ = lean_st_ref_take(v___y_2059_);
v_currNamespace_2061_ = lean_ctor_get(v___y_2058_, 5);
v_openDecls_2062_ = lean_ctor_get(v___y_2058_, 6);
v_env_2063_ = lean_ctor_get(v___x_2060_, 0);
v_nextMacroScope_2064_ = lean_ctor_get(v___x_2060_, 1);
v_ngen_2065_ = lean_ctor_get(v___x_2060_, 2);
v_auxDeclNGen_2066_ = lean_ctor_get(v___x_2060_, 3);
v_traceState_2067_ = lean_ctor_get(v___x_2060_, 4);
v_cache_2068_ = lean_ctor_get(v___x_2060_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2060_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2060_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2060_, 8);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2073_ = v___x_2060_;
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2067_);
lean_inc(v_auxDeclNGen_2066_);
lean_inc(v_ngen_2065_);
lean_inc(v_nextMacroScope_2064_);
lean_inc(v_env_2063_);
lean_dec(v___x_2060_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_inc(v_openDecls_2062_);
lean_inc(v_currNamespace_2061_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_currNamespace_2061_);
lean_ctor_set(v___x_2075_, 1, v_openDecls_2062_);
v___x_2076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___y_2055_);
lean_inc_ref(v___y_2052_);
lean_inc_ref(v___y_2053_);
v___x_2077_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2077_, 0, v___y_2053_);
lean_ctor_set(v___x_2077_, 1, v___y_2057_);
lean_ctor_set(v___x_2077_, 2, v___y_2056_);
lean_ctor_set(v___x_2077_, 3, v___y_2052_);
lean_ctor_set(v___x_2077_, 4, v___x_2076_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5, v___y_2054_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5 + 1, v___y_2051_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5 + 2, v_isSilent_2044_);
v___x_2078_ = l_Lean_MessageLog_add(v___x_2077_, v_messages_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 6, v___x_2078_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_env_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_nextMacroScope_2064_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_ngen_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_auxDeclNGen_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_traceState_2067_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2084_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2084_, 8, v_snapshotTasks_2071_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_st_ref_put(v___y_2059_, v___x_2080_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
v___jp_2086_:
{
lean_object* v_fileName_2094_; lean_object* v_fileMap_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2111_; 
v_fileName_2094_ = lean_ctor_get(v___y_2089_, 0);
v_fileMap_2095_ = lean_ctor_get(v___y_2089_, 1);
v___x_2096_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2042_);
v___x_2097_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_2096_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2111_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_inc_ref_n(v_fileMap_2095_, 2);
v___x_2102_ = l_Lean_FileMap_toPosition(v_fileMap_2095_, v___y_2090_);
lean_dec(v___y_2090_);
v___x_2103_ = l_Lean_FileMap_toPosition(v_fileMap_2095_, v___y_2093_);
lean_dec(v___y_2093_);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
v___x_2105_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0));
if (v___y_2092_ == 0)
{
lean_del_object(v___x_2100_);
lean_dec_ref(v___y_2087_);
v___y_2051_ = v___y_2088_;
v___y_2052_ = v___x_2105_;
v___y_2053_ = v_fileName_2094_;
v___y_2054_ = v___y_2091_;
v___y_2055_ = v_a_2098_;
v___y_2056_ = v___x_2104_;
v___y_2057_ = v___x_2102_;
v___y_2058_ = v___y_2047_;
v___y_2059_ = v___y_2048_;
goto v___jp_2050_;
}
else
{
uint8_t v___x_2106_; 
lean_inc(v_a_2098_);
v___x_2106_ = l_Lean_MessageData_hasTag(v___y_2087_, v_a_2098_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec_ref_known(v___x_2104_, 1);
lean_dec_ref(v___x_2102_);
lean_dec(v_a_2098_);
v___x_2107_ = lean_box(0);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2107_);
v___x_2109_ = v___x_2100_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_del_object(v___x_2100_);
v___y_2051_ = v___y_2088_;
v___y_2052_ = v___x_2105_;
v___y_2053_ = v_fileName_2094_;
v___y_2054_ = v___y_2091_;
v___y_2055_ = v_a_2098_;
v___y_2056_ = v___x_2104_;
v___y_2057_ = v___x_2102_;
v___y_2058_ = v___y_2047_;
v___y_2059_ = v___y_2048_;
goto v___jp_2050_;
}
}
}
}
v___jp_2112_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Syntax_getTailPos_x3f(v___y_2114_, v___y_2117_);
lean_dec(v___y_2114_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_inc(v___y_2119_);
v___y_2087_ = v___y_2113_;
v___y_2088_ = v___y_2116_;
v___y_2089_ = v___y_2115_;
v___y_2090_ = v___y_2119_;
v___y_2091_ = v___y_2117_;
v___y_2092_ = v___y_2118_;
v___y_2093_ = v___y_2119_;
goto v___jp_2086_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___y_2087_ = v___y_2113_;
v___y_2088_ = v___y_2116_;
v___y_2089_ = v___y_2115_;
v___y_2090_ = v___y_2119_;
v___y_2091_ = v___y_2117_;
v___y_2092_ = v___y_2118_;
v___y_2093_ = v_val_2121_;
goto v___jp_2086_;
}
}
v___jp_2122_:
{
lean_object* v_ref_2129_; lean_object* v___x_2130_; 
v_ref_2129_ = l_Lean_replaceRef(v_ref_2041_, v___y_2124_);
v___x_2130_ = l_Lean_Syntax_getPos_x3f(v_ref_2129_, v___y_2126_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v___y_2113_ = v___y_2123_;
v___y_2114_ = v_ref_2129_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v___y_2126_;
v___y_2118_ = v___y_2127_;
v___y_2119_ = v___x_2131_;
goto v___jp_2112_;
}
else
{
lean_object* v_val_2132_; 
v_val_2132_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2113_ = v___y_2123_;
v___y_2114_ = v_ref_2129_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v___y_2126_;
v___y_2118_ = v___y_2127_;
v___y_2119_ = v_val_2132_;
goto v___jp_2112_;
}
}
v___jp_2134_:
{
if (v___y_2140_ == 0)
{
v___y_2123_ = v___y_2135_;
v___y_2124_ = v___y_2136_;
v___y_2125_ = v___y_2137_;
v___y_2126_ = v___y_2139_;
v___y_2127_ = v___y_2138_;
v___y_2128_ = v_severity_2043_;
goto v___jp_2122_;
}
else
{
v___y_2123_ = v___y_2135_;
v___y_2124_ = v___y_2136_;
v___y_2125_ = v___y_2137_;
v___y_2126_ = v___y_2139_;
v___y_2127_ = v___y_2138_;
v___y_2128_ = v___x_2133_;
goto v___jp_2122_;
}
}
v___jp_2141_:
{
if (v___y_2142_ == 0)
{
lean_object* v_toCold_2143_; lean_object* v_options_2144_; lean_object* v_ref_2145_; uint8_t v_suppressElabErrors_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; uint8_t v___x_2150_; uint8_t v___x_2151_; 
v_toCold_2143_ = lean_ctor_get(v___y_2047_, 0);
v_options_2144_ = lean_ctor_get(v___y_2047_, 1);
v_ref_2145_ = lean_ctor_get(v___y_2047_, 4);
v_suppressElabErrors_2146_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*10 + 1);
v___x_2147_ = lean_box(v_suppressElabErrors_2146_);
v___x_2148_ = lean_box(v___y_2142_);
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2149_, 0, v___x_2147_);
lean_closure_set(v___f_2149_, 1, v___x_2148_);
v___x_2150_ = 1;
v___x_2151_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2043_, v___x_2150_);
if (v___x_2151_ == 0)
{
v___y_2135_ = v___f_2149_;
v___y_2136_ = v_ref_2145_;
v___y_2137_ = v_toCold_2143_;
v___y_2138_ = v_suppressElabErrors_2146_;
v___y_2139_ = v___y_2142_;
v___y_2140_ = v___x_2151_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = l_Lean_warningAsError;
v___x_2153_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_2144_, v___x_2152_);
v___y_2135_ = v___f_2149_;
v___y_2136_ = v_ref_2145_;
v___y_2137_ = v_toCold_2143_;
v___y_2138_ = v_suppressElabErrors_2146_;
v___y_2139_ = v___y_2142_;
v___y_2140_ = v___x_2153_;
goto v___jp_2134_;
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_msgData_2042_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object* v_ref_2158_, lean_object* v_msgData_2159_, lean_object* v_severity_2160_, lean_object* v_isSilent_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_severity_boxed_2167_; uint8_t v_isSilent_boxed_2168_; lean_object* v_res_2169_; 
v_severity_boxed_2167_ = lean_unbox(v_severity_2160_);
v_isSilent_boxed_2168_ = lean_unbox(v_isSilent_2161_);
v_res_2169_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2158_, v_msgData_2159_, v_severity_boxed_2167_, v_isSilent_boxed_2168_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v_ref_2158_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object* v_msgData_2170_, uint8_t v_severity_2171_, uint8_t v_isSilent_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_ref_2178_; lean_object* v___x_2179_; 
v_ref_2178_ = lean_ctor_get(v___y_2175_, 4);
v___x_2179_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2178_, v_msgData_2170_, v_severity_2171_, v_isSilent_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object* v_msgData_2180_, lean_object* v_severity_2181_, lean_object* v_isSilent_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_severity_boxed_2188_; uint8_t v_isSilent_boxed_2189_; lean_object* v_res_2190_; 
v_severity_boxed_2188_ = lean_unbox(v_severity_2181_);
v_isSilent_boxed_2189_ = lean_unbox(v_isSilent_2182_);
v_res_2190_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2180_, v_severity_boxed_2188_, v_isSilent_boxed_2189_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object* v_msgData_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = 2;
v___x_2198_ = 0;
v___x_2199_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2191_, v___x_2197_, v___x_2198_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object* v_msgData_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object* v___y_2207_, uint8_t v_isExporting_2208_, lean_object* v___x_2209_, lean_object* v___y_2210_, lean_object* v___x_2211_, lean_object* v_a_x3f_2212_){
_start:
{
lean_object* v___x_2214_; lean_object* v_env_2215_; lean_object* v_nextMacroScope_2216_; lean_object* v_ngen_2217_; lean_object* v_auxDeclNGen_2218_; lean_object* v_traceState_2219_; lean_object* v_messages_2220_; lean_object* v_infoState_2221_; lean_object* v_snapshotTasks_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2247_; 
v___x_2214_ = lean_st_ref_take(v___y_2207_);
v_env_2215_ = lean_ctor_get(v___x_2214_, 0);
v_nextMacroScope_2216_ = lean_ctor_get(v___x_2214_, 1);
v_ngen_2217_ = lean_ctor_get(v___x_2214_, 2);
v_auxDeclNGen_2218_ = lean_ctor_get(v___x_2214_, 3);
v_traceState_2219_ = lean_ctor_get(v___x_2214_, 4);
v_messages_2220_ = lean_ctor_get(v___x_2214_, 6);
v_infoState_2221_ = lean_ctor_get(v___x_2214_, 7);
v_snapshotTasks_2222_ = lean_ctor_get(v___x_2214_, 8);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2214_, 5);
lean_dec(v_unused_2248_);
v___x_2224_ = v___x_2214_;
v_isShared_2225_ = v_isSharedCheck_2247_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_snapshotTasks_2222_);
lean_inc(v_infoState_2221_);
lean_inc(v_messages_2220_);
lean_inc(v_traceState_2219_);
lean_inc(v_auxDeclNGen_2218_);
lean_inc(v_ngen_2217_);
lean_inc(v_nextMacroScope_2216_);
lean_inc(v_env_2215_);
lean_dec(v___x_2214_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2247_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = l_Lean_Environment_setExporting(v_env_2215_, v_isExporting_2208_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 5, v___x_2209_);
lean_ctor_set(v___x_2224_, 0, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_nextMacroScope_2216_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_ngen_2217_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_auxDeclNGen_2218_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_traceState_2219_);
lean_ctor_set(v_reuseFailAlloc_2246_, 5, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2246_, 6, v_messages_2220_);
lean_ctor_set(v_reuseFailAlloc_2246_, 7, v_infoState_2221_);
lean_ctor_set(v_reuseFailAlloc_2246_, 8, v_snapshotTasks_2222_);
v___x_2228_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_mctx_2231_; lean_object* v_zetaDeltaFVarIds_2232_; lean_object* v_postponed_2233_; lean_object* v_diag_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2244_; 
v___x_2229_ = lean_st_ref_put(v___y_2207_, v___x_2228_);
v___x_2230_ = lean_st_ref_take(v___y_2210_);
v_mctx_2231_ = lean_ctor_get(v___x_2230_, 0);
v_zetaDeltaFVarIds_2232_ = lean_ctor_get(v___x_2230_, 2);
v_postponed_2233_ = lean_ctor_get(v___x_2230_, 3);
v_diag_2234_ = lean_ctor_get(v___x_2230_, 4);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2230_, 1);
lean_dec(v_unused_2245_);
v___x_2236_ = v___x_2230_;
v_isShared_2237_ = v_isSharedCheck_2244_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_diag_2234_);
lean_inc(v_postponed_2233_);
lean_inc(v_zetaDeltaFVarIds_2232_);
lean_inc(v_mctx_2231_);
lean_dec(v___x_2230_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2244_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2211_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_mctx_2231_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_zetaDeltaFVarIds_2232_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_postponed_2233_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_diag_2234_);
v___x_2239_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_st_ref_put(v___y_2210_, v___x_2239_);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object* v___y_2249_, lean_object* v_isExporting_2250_, lean_object* v___x_2251_, lean_object* v___y_2252_, lean_object* v___x_2253_, lean_object* v_a_x3f_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v_isExporting_boxed_2256_; lean_object* v_res_2257_; 
v_isExporting_boxed_2256_ = lean_unbox(v_isExporting_2250_);
v_res_2257_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2249_, v_isExporting_boxed_2256_, v___x_2251_, v___y_2252_, v___x_2253_, v_a_x3f_2254_);
lean_dec(v_a_x3f_2254_);
lean_dec(v___y_2252_);
lean_dec(v___y_2249_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object* v_declName_2258_, uint8_t v_isExporting_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v_env_2265_; lean_object* v___x_2266_; uint8_t v_isModule_2267_; 
v___x_2264_ = lean_st_ref_get(v___y_2262_);
v_env_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_ref(v_env_2265_);
lean_dec(v___x_2264_);
v___x_2266_ = l_Lean_Environment_header(v_env_2265_);
v_isModule_2267_ = lean_ctor_get_uint8(v___x_2266_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2266_);
if (v_isModule_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec_ref(v_env_2265_);
v___x_2268_ = l_Lean_validateDefEqAttr(v_declName_2258_, v___y_2261_, v___y_2262_);
return v___x_2268_;
}
else
{
uint8_t v_isExporting_2269_; 
v_isExporting_2269_ = lean_ctor_get_uint8(v_env_2265_, sizeof(void*)*8);
lean_dec_ref(v_env_2265_);
if (v_isExporting_2259_ == 0)
{
if (v_isExporting_2269_ == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_validateDefEqAttr(v_declName_2258_, v___y_2261_, v___y_2262_);
return v___x_2335_;
}
else
{
goto v___jp_2270_;
}
}
else
{
if (v_isExporting_2269_ == 0)
{
goto v___jp_2270_;
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_validateDefEqAttr(v_declName_2258_, v___y_2261_, v___y_2262_);
return v___x_2336_;
}
}
v___jp_2270_:
{
lean_object* v___x_2271_; lean_object* v_env_2272_; lean_object* v_nextMacroScope_2273_; lean_object* v_ngen_2274_; lean_object* v_auxDeclNGen_2275_; lean_object* v_traceState_2276_; lean_object* v_messages_2277_; lean_object* v_infoState_2278_; lean_object* v_snapshotTasks_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2333_; 
v___x_2271_ = lean_st_ref_take(v___y_2262_);
v_env_2272_ = lean_ctor_get(v___x_2271_, 0);
v_nextMacroScope_2273_ = lean_ctor_get(v___x_2271_, 1);
v_ngen_2274_ = lean_ctor_get(v___x_2271_, 2);
v_auxDeclNGen_2275_ = lean_ctor_get(v___x_2271_, 3);
v_traceState_2276_ = lean_ctor_get(v___x_2271_, 4);
v_messages_2277_ = lean_ctor_get(v___x_2271_, 6);
v_infoState_2278_ = lean_ctor_get(v___x_2271_, 7);
v_snapshotTasks_2279_ = lean_ctor_get(v___x_2271_, 8);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v___x_2271_, 5);
lean_dec(v_unused_2334_);
v___x_2281_ = v___x_2271_;
v_isShared_2282_ = v_isSharedCheck_2333_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_snapshotTasks_2279_);
lean_inc(v_infoState_2278_);
lean_inc(v_messages_2277_);
lean_inc(v_traceState_2276_);
lean_inc(v_auxDeclNGen_2275_);
lean_inc(v_ngen_2274_);
lean_inc(v_nextMacroScope_2273_);
lean_inc(v_env_2272_);
lean_dec(v___x_2271_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2333_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = l_Lean_Environment_setExporting(v_env_2272_, v_isExporting_2259_);
v___x_2284_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 5, v___x_2284_);
lean_ctor_set(v___x_2281_, 0, v___x_2283_);
v___x_2286_ = v___x_2281_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_nextMacroScope_2273_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_ngen_2274_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_auxDeclNGen_2275_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_traceState_2276_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_messages_2277_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_infoState_2278_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_snapshotTasks_2279_);
v___x_2286_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_mctx_2289_; lean_object* v_zetaDeltaFVarIds_2290_; lean_object* v_postponed_2291_; lean_object* v_diag_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2330_; 
v___x_2287_ = lean_st_ref_put(v___y_2262_, v___x_2286_);
v___x_2288_ = lean_st_ref_take(v___y_2260_);
v_mctx_2289_ = lean_ctor_get(v___x_2288_, 0);
v_zetaDeltaFVarIds_2290_ = lean_ctor_get(v___x_2288_, 2);
v_postponed_2291_ = lean_ctor_get(v___x_2288_, 3);
v_diag_2292_ = lean_ctor_get(v___x_2288_, 4);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2288_, 1);
lean_dec(v_unused_2331_);
v___x_2294_ = v___x_2288_;
v_isShared_2295_ = v_isSharedCheck_2330_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_diag_2292_);
lean_inc(v_postponed_2291_);
lean_inc(v_zetaDeltaFVarIds_2290_);
lean_inc(v_mctx_2289_);
lean_dec(v___x_2288_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2330_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_mctx_2289_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_zetaDeltaFVarIds_2290_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_postponed_2291_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v_diag_2292_);
v___x_2298_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v_r_2300_; 
v___x_2299_ = lean_st_ref_put(v___y_2260_, v___x_2298_);
v_r_2300_ = l_Lean_validateDefEqAttr(v_declName_2258_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v_r_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2317_; 
v_a_2301_ = lean_ctor_get(v_r_2300_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_r_2300_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2303_ = v_r_2300_;
v_isShared_2304_ = v_isSharedCheck_2317_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v_r_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2317_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
lean_inc(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 1);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v___x_2307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2262_, v_isExporting_2269_, v___x_2284_, v___y_2260_, v___x_2296_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v___x_2307_, 0);
lean_dec(v_unused_2315_);
v___x_2309_ = v___x_2307_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v_a_2301_);
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2301_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_a_2318_ = lean_ctor_get(v_r_2300_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v_r_2300_, 1);
v___x_2319_ = lean_box(0);
v___x_2320_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2262_, v_isExporting_2269_, v___x_2284_, v___y_2260_, v___x_2296_, v___x_2319_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2320_, 0);
lean_dec(v_unused_2328_);
v___x_2322_ = v___x_2320_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_dec(v___x_2320_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set_tag(v___x_2322_, 1);
lean_ctor_set(v___x_2322_, 0, v_a_2318_);
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2318_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object* v_declName_2337_, lean_object* v_isExporting_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v_isExporting_boxed_2343_; lean_object* v_res_2344_; 
v_isExporting_boxed_2343_ = lean_unbox(v_isExporting_2338_);
v_res_2344_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2337_, v_isExporting_boxed_2343_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object* v_declName_2345_, uint8_t v_isExporting_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2345_, v_isExporting_2346_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object* v_declName_2353_, lean_object* v_isExporting_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_isExporting_boxed_2360_; lean_object* v_res_2361_; 
v_isExporting_boxed_2360_ = lean_unbox(v_isExporting_2354_);
v_res_2361_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2353_, v_isExporting_boxed_2360_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* v_lhs_2362_, lean_object* v_rhs_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___y_2370_; lean_object* v___x_2387_; uint8_t v_transparency_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; 
v___x_2387_ = l_Lean_Meta_Context_config(v___y_2364_);
v_transparency_2388_ = lean_ctor_get_uint8(v___x_2387_, 9);
lean_dec_ref(v___x_2387_);
v___x_2389_ = 5;
v___x_2390_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v_keyedConfig_2391_; uint8_t v_trackZetaDelta_2392_; lean_object* v_zetaDeltaSet_2393_; lean_object* v_lctx_2394_; lean_object* v_localInstances_2395_; lean_object* v_defEqCtx_x3f_2396_; lean_object* v_synthPendingDepth_2397_; lean_object* v_customCanUnfoldPredicate_x3f_2398_; uint8_t v_univApprox_2399_; uint8_t v_inTypeClassResolution_2400_; uint8_t v_cacheInferType_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_keyedConfig_2391_ = lean_ctor_get(v___y_2364_, 0);
v_trackZetaDelta_2392_ = lean_ctor_get_uint8(v___y_2364_, sizeof(void*)*7);
v_zetaDeltaSet_2393_ = lean_ctor_get(v___y_2364_, 1);
v_lctx_2394_ = lean_ctor_get(v___y_2364_, 2);
v_localInstances_2395_ = lean_ctor_get(v___y_2364_, 3);
v_defEqCtx_x3f_2396_ = lean_ctor_get(v___y_2364_, 4);
v_synthPendingDepth_2397_ = lean_ctor_get(v___y_2364_, 5);
v_customCanUnfoldPredicate_x3f_2398_ = lean_ctor_get(v___y_2364_, 6);
v_univApprox_2399_ = lean_ctor_get_uint8(v___y_2364_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2400_ = lean_ctor_get_uint8(v___y_2364_, sizeof(void*)*7 + 2);
v_cacheInferType_2401_ = lean_ctor_get_uint8(v___y_2364_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2391_);
v___x_2402_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2389_, v_keyedConfig_2391_);
lean_inc(v_customCanUnfoldPredicate_x3f_2398_);
lean_inc(v_synthPendingDepth_2397_);
lean_inc(v_defEqCtx_x3f_2396_);
lean_inc_ref(v_localInstances_2395_);
lean_inc_ref(v_lctx_2394_);
lean_inc(v_zetaDeltaSet_2393_);
v___x_2403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_zetaDeltaSet_2393_);
lean_ctor_set(v___x_2403_, 2, v_lctx_2394_);
lean_ctor_set(v___x_2403_, 3, v_localInstances_2395_);
lean_ctor_set(v___x_2403_, 4, v_defEqCtx_x3f_2396_);
lean_ctor_set(v___x_2403_, 5, v_synthPendingDepth_2397_);
lean_ctor_set(v___x_2403_, 6, v_customCanUnfoldPredicate_x3f_2398_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7, v_trackZetaDelta_2392_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 1, v_univApprox_2399_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2400_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 3, v_cacheInferType_2401_);
v___x_2404_ = l_Lean_Meta_isExprDefEq(v_lhs_2362_, v_rhs_2363_, v___x_2403_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref_known(v___x_2403_, 7);
v___y_2370_ = v___x_2404_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Meta_isExprDefEq(v_lhs_2362_, v_rhs_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
v___y_2370_ = v___x_2405_;
goto v___jp_2369_;
}
v___jp_2369_:
{
if (lean_obj_tag(v___y_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___y_2370_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___y_2370_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___y_2370_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___y_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_a_2379_ = lean_ctor_get(v___y_2370_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___y_2370_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___y_2370_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___y_2370_);
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
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* v_lhs_2406_, lean_object* v_rhs_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2406_, v_rhs_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__0));
v___x_2416_ = l_Lean_stringToMessageData(v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__2));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* v_declName_2420_, lean_object* v___f_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___x_2437_; 
lean_inc(v_declName_2420_);
v___x_2437_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_declName_2420_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_n(v_a_2438_, 2);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = 1;
v___x_2440_ = l_Lean_ConstantInfo_value_x3f(v_a_2438_, v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = l_Lean_ConstantInfo_type(v_a_2438_);
lean_dec(v_a_2438_);
v___x_2443_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v___x_2442_, v_val_2441_, v___y_2425_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; uint8_t v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_unbox(v_a_2444_);
if (v___x_2445_ == 0)
{
lean_dec(v_a_2444_);
lean_dec_ref(v___x_2442_);
lean_dec_ref(v___f_2421_);
lean_dec(v_declName_2420_);
goto v___jp_2434_;
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v___x_2442_, v___f_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___y_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; uint8_t v___y_2457_; uint8_t v___y_2469_; uint8_t v___x_2474_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2474_ = l_Lean_isPrivateName(v_declName_2420_);
if (v___x_2474_ == 0)
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_unbox(v_a_2444_);
lean_dec(v_a_2444_);
v___y_2469_ = v___x_2475_;
goto v___jp_2468_;
}
else
{
uint8_t v___x_2476_; 
lean_dec(v_a_2444_);
v___x_2476_ = 0;
v___y_2469_ = v___x_2476_;
goto v___jp_2468_;
}
v___jp_2448_:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
if (v___x_2449_ == 0)
{
v___y_2428_ = v___y_2422_;
v___y_2429_ = v___y_2423_;
v___y_2430_ = v___y_2424_;
v___y_2431_ = v___y_2425_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = l_Lean_defeqAttr;
lean_inc(v_declName_2420_);
v___x_2451_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2450_, v_declName_2420_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref_known(v___x_2451_, 1);
v___y_2428_ = v___y_2422_;
v___y_2429_ = v___y_2423_;
v___y_2430_ = v___y_2424_;
v___y_2431_ = v___y_2425_;
goto v___jp_2427_;
}
else
{
lean_dec(v_declName_2420_);
return v___x_2451_;
}
}
}
v___jp_2452_:
{
if (lean_obj_tag(v___y_2453_) == 0)
{
lean_dec_ref_known(v___y_2453_, 1);
goto v___jp_2448_;
}
else
{
lean_dec(v_a_2447_);
lean_dec(v_declName_2420_);
return v___y_2453_;
}
}
v___jp_2454_:
{
if (v___y_2457_ == 0)
{
uint8_t v___x_2458_; 
lean_dec_ref(v___y_2455_);
v___x_2458_ = lean_unbox(v_a_2447_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2459_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__1, &l_Lean_inferDefEqAttr___lam__1___closed__1_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__1);
lean_inc(v_declName_2420_);
v___x_2460_ = l_Lean_MessageData_ofName(v_declName_2420_);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__3, &l_Lean_inferDefEqAttr___lam__1___closed__3_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__3);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_Exception_toMessageData(v___y_2456_);
v___x_2465_ = l_Lean_indentD(v___x_2464_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v___x_2466_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v___y_2453_ = v___x_2467_;
goto v___jp_2452_;
}
else
{
lean_dec_ref(v___y_2456_);
goto v___jp_2448_;
}
}
else
{
lean_dec_ref(v___y_2456_);
v___y_2453_ = v___y_2455_;
goto v___jp_2452_;
}
}
v___jp_2468_:
{
lean_object* v___x_2470_; 
lean_inc(v_declName_2420_);
v___x_2470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2420_, v___y_2469_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2470_) == 0)
{
v___y_2453_ = v___x_2470_;
goto v___jp_2452_;
}
else
{
lean_object* v_a_2471_; uint8_t v___x_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
v___x_2472_ = l_Lean_Exception_isInterrupt(v_a_2471_);
if (v___x_2472_ == 0)
{
uint8_t v___x_2473_; 
lean_inc(v_a_2471_);
v___x_2473_ = l_Lean_Exception_isRuntime(v_a_2471_);
v___y_2455_ = v___x_2470_;
v___y_2456_ = v_a_2471_;
v___y_2457_ = v___x_2473_;
goto v___jp_2454_;
}
else
{
v___y_2455_ = v___x_2470_;
v___y_2456_ = v_a_2471_;
v___y_2457_ = v___x_2472_;
goto v___jp_2454_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2444_);
lean_dec(v_declName_2420_);
v_a_2477_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2446_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2446_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v___x_2442_);
lean_dec_ref(v___f_2421_);
lean_dec(v_declName_2420_);
v_a_2485_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2443_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2443_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_dec(v___x_2440_);
lean_dec(v_a_2438_);
lean_dec_ref(v___f_2421_);
lean_dec(v_declName_2420_);
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v___f_2421_);
lean_dec(v_declName_2420_);
v_a_2493_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2437_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2437_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
v___jp_2427_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = l_Lean_backwardDefeqAttr;
v___x_2433_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2432_, v_declName_2420_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
v___jp_2434_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object* v_declName_2501_, lean_object* v___f_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2501_, v___f_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object* v_declName_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___f_2516_; lean_object* v___f_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; 
v___f_2516_ = ((lean_object*)(l_Lean_inferDefEqAttr___closed__0));
v___f_2517_ = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2517_, 0, v_declName_2510_);
lean_closure_set(v___f_2517_, 1, v___f_2516_);
v___x_2518_ = 1;
v___x_2519_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___f_2517_, v___x_2518_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object* v_declName_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_inferDefEqAttr(v_declName_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_2527_, lean_object* v_attrName_2528_, lean_object* v_declName_2529_, lean_object* v_asyncPrefix_x3f_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_2528_, v_declName_2529_, v_asyncPrefix_x3f_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_attrName_2538_, lean_object* v_declName_2539_, lean_object* v_asyncPrefix_x3f_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_2537_, v_attrName_2538_, v_declName_2539_, v_asyncPrefix_x3f_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object* v_00_u03b1_2547_, lean_object* v_attrName_2548_, lean_object* v_declName_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_2548_, v_declName_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_attrName_2557_, lean_object* v_declName_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_2556_, v_attrName_2557_, v_declName_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object* v_00_u03b1_2565_, lean_object* v_constName_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_constName_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_2573_, v_constName_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object* v_00_u03b1_2581_, lean_object* v_ref_2582_, lean_object* v_constName_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2582_, v_constName_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_ref_2591_, lean_object* v_constName_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_2590_, v_ref_2591_, v_constName_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v_ref_2591_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object* v_00_u03b1_2599_, lean_object* v_ref_2600_, lean_object* v_msg_2601_, lean_object* v_declHint_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2600_, v_msg_2601_, v_declHint_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2609_, lean_object* v_ref_2610_, lean_object* v_msg_2611_, lean_object* v_declHint_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_2609_, v_ref_2610_, v_msg_2611_, v_declHint_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v_ref_2610_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(lean_object* v_msg_2619_, lean_object* v_declHint_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_2619_, v_declHint_2620_, v___y_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___boxed(lean_object* v_msg_2627_, lean_object* v_declHint_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(v_msg_2627_, v_declHint_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_2635_, lean_object* v_ref_2636_, lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2636_, v_msg_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_ref_2645_, lean_object* v_msg_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_2644_, v_ref_2645_, v_msg_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v_ref_2645_);
return v_res_2652_;
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
