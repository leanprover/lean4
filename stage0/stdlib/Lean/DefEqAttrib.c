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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26;
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
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_59_;
v_res_59_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(lean_object* v_opts_62_, lean_object* v_opt_63_){
_start:
{
lean_object* v_name_64_; lean_object* v_defValue_65_; lean_object* v_map_66_; lean_object* v___x_67_; 
v_name_64_ = lean_ctor_get(v_opt_63_, 0);
v_defValue_65_ = lean_ctor_get(v_opt_63_, 1);
v_map_66_ = lean_ctor_get(v_opts_62_, 0);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_66_, v_name_64_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_inc(v_defValue_65_);
return v_defValue_65_;
}
else
{
lean_object* v_val_68_; 
v_val_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v___x_67_, 1);
if (lean_obj_tag(v_val_68_) == 3)
{
lean_object* v_v_69_; 
v_v_69_ = lean_ctor_get(v_val_68_, 0);
lean_inc(v_v_69_);
lean_dec_ref_known(v_val_68_, 1);
return v_v_69_;
}
else
{
lean_dec(v_val_68_);
lean_inc(v_defValue_65_);
return v_defValue_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(lean_object* v_opts_70_, lean_object* v_opt_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_opts_70_, v_opt_71_);
lean_dec_ref(v_opt_71_);
lean_dec_ref(v_opts_70_);
return v_res_72_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(lean_object* v_o_76_, lean_object* v_k_77_, uint8_t v_v_78_){
_start:
{
lean_object* v_map_79_; uint8_t v_hasTrace_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_94_; 
v_map_79_ = lean_ctor_get(v_o_76_, 0);
v_hasTrace_80_ = lean_ctor_get_uint8(v_o_76_, sizeof(void*)*1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_o_76_);
if (v_isSharedCheck_94_ == 0)
{
v___x_82_ = v_o_76_;
v_isShared_83_ = v_isSharedCheck_94_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_map_79_);
lean_dec(v_o_76_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_94_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_84_, 0, v_v_78_);
lean_inc(v_k_77_);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_77_, v___x_84_, v_map_79_);
if (v_hasTrace_80_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_89_; 
v___x_86_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__1));
v___x_87_ = l_Lean_Name_isPrefixOf(v___x_86_, v_k_77_);
lean_dec(v_k_77_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_89_ = v___x_82_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_85_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_87_);
return v___x_89_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_k_77_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_92_ = v___x_82_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_93_, sizeof(void*)*1, v_hasTrace_80_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_76_ = stack[0].m_obj;
lean_object* v_k_77_ = stack[1].m_obj;
uint8_t v_v_78_ = stack[2].m_num;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(v_o_76_, v_k_77_, v_v_78_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___boxed(lean_object* v_o_96_, lean_object* v_k_97_, lean_object* v_v_98_){
_start:
{
uint8_t v_v_boxed_99_; lean_object* v_res_100_; 
v_v_boxed_99_ = lean_unbox(v_v_98_);
v_res_100_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(v_o_96_, v_k_97_, v_v_boxed_99_);
return v_res_100_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(lean_object* v_opts_101_, lean_object* v_opt_102_, uint8_t v_val_103_){
_start:
{
lean_object* v_name_104_; lean_object* v___x_105_; 
v_name_104_ = lean_ctor_get(v_opt_102_, 0);
lean_inc(v_name_104_);
lean_dec_ref(v_opt_102_);
v___x_105_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1(v_opts_101_, v_name_104_, v_val_103_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_101_ = stack[0].m_obj;
lean_object* v_opt_102_ = stack[1].m_obj;
uint8_t v_val_103_ = stack[2].m_num;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_opts_101_, v_opt_102_, v_val_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(lean_object* v_opts_107_, lean_object* v_opt_108_, lean_object* v_val_109_){
_start:
{
uint8_t v_val_boxed_110_; lean_object* v_res_111_; 
v_val_boxed_110_ = lean_unbox(v_val_109_);
v_res_111_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_opts_107_, v_opt_108_, v_val_boxed_110_);
return v_res_111_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
return v___x_116_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object* v_e1_117_, lean_object* v_e2_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___y_125_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v_toCold_182_; lean_object* v_currRecDepth_183_; lean_object* v_ref_184_; uint8_t v_suppressElabErrors_185_; uint8_t v_isRecordingDeps_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_options_189_; lean_object* v_currNamespace_190_; lean_object* v_openDecls_191_; lean_object* v_initHeartbeats_192_; lean_object* v_maxHeartbeats_193_; lean_object* v_quotContext_194_; lean_object* v_currMacroScope_195_; lean_object* v_cancelTk_x3f_196_; lean_object* v_inheritedTraceOptions_197_; uint8_t v___x_198_; lean_object* v___y_200_; uint16_t v___y_201_; lean_object* v_fileName_202_; lean_object* v_fileMap_203_; lean_object* v_currNamespace_204_; lean_object* v_openDecls_205_; lean_object* v_initHeartbeats_206_; lean_object* v_maxHeartbeats_207_; lean_object* v_quotContext_208_; lean_object* v_currMacroScope_209_; lean_object* v_cancelTk_x3f_210_; lean_object* v_inheritedTraceOptions_211_; lean_object* v_currRecDepth_212_; lean_object* v_ref_213_; uint8_t v_suppressElabErrors_214_; uint8_t v_isRecordingDeps_215_; lean_object* v___y_216_; uint8_t v___y_240_; lean_object* v___y_241_; uint16_t v___y_242_; lean_object* v___y_265_; 
v_toCold_182_ = lean_ctor_get(v_a_121_, 0);
v_currRecDepth_183_ = lean_ctor_get(v_a_121_, 1);
v_ref_184_ = lean_ctor_get(v_a_121_, 2);
v_suppressElabErrors_185_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*3 + 2);
v_isRecordingDeps_186_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*3 + 3);
v_fileName_187_ = lean_ctor_get(v_toCold_182_, 0);
v_fileMap_188_ = lean_ctor_get(v_toCold_182_, 1);
v_options_189_ = lean_ctor_get(v_toCold_182_, 2);
v_currNamespace_190_ = lean_ctor_get(v_toCold_182_, 4);
v_openDecls_191_ = lean_ctor_get(v_toCold_182_, 5);
v_initHeartbeats_192_ = lean_ctor_get(v_toCold_182_, 6);
v_maxHeartbeats_193_ = lean_ctor_get(v_toCold_182_, 7);
v_quotContext_194_ = lean_ctor_get(v_toCold_182_, 8);
v_currMacroScope_195_ = lean_ctor_get(v_toCold_182_, 9);
v_cancelTk_x3f_196_ = lean_ctor_get(v_toCold_182_, 10);
v_inheritedTraceOptions_197_ = lean_ctor_get(v_toCold_182_, 11);
v___x_198_ = 1;
if (v_isRecordingDeps_186_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_189_);
v___x_277_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_189_, v___x_276_, v_isRecordingDeps_186_);
v___y_265_ = v___x_277_;
goto v___jp_264_;
}
else
{
lean_object* v___x_278_; 
lean_inc_ref(v_options_189_);
v___x_278_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_189_);
v___y_265_ = v___x_278_;
goto v___jp_264_;
}
v___jp_124_:
{
if (lean_obj_tag(v___y_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_126_ = lean_ctor_get(v___y_125_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___y_125_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___y_125_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___y_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___y_125_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___y_125_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___y_125_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___y_125_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
v___jp_142_:
{
if (lean_obj_tag(v___y_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_173_; 
v_a_146_ = lean_ctor_get(v___y_145_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___y_145_);
if (v_isSharedCheck_173_ == 0)
{
v___x_148_ = v___y_145_;
v_isShared_149_ = v_isSharedCheck_173_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___y_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_173_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v_a_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; uint8_t v_transparency_152_; uint8_t v___x_153_; uint8_t v___x_154_; 
lean_del_object(v___x_148_);
lean_dec(v_a_146_);
v___x_151_ = l_Lean_Meta_Context_config(v_a_119_);
v_transparency_152_ = lean_ctor_get_uint8(v___x_151_, 9);
lean_dec_ref(v___x_151_);
v___x_153_ = 0;
v___x_154_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v_keyedConfig_155_; uint8_t v_trackZetaDelta_156_; lean_object* v_zetaDeltaSet_157_; lean_object* v_lctx_158_; lean_object* v_localInstances_159_; lean_object* v_defEqCtx_x3f_160_; lean_object* v_synthPendingDepth_161_; lean_object* v_customCanUnfoldPredicate_x3f_162_; uint8_t v_univApprox_163_; uint8_t v_inTypeClassResolution_164_; uint8_t v_cacheInferType_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_keyedConfig_155_ = lean_ctor_get(v_a_119_, 0);
v_trackZetaDelta_156_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7);
v_zetaDeltaSet_157_ = lean_ctor_get(v_a_119_, 1);
v_lctx_158_ = lean_ctor_get(v_a_119_, 2);
v_localInstances_159_ = lean_ctor_get(v_a_119_, 3);
v_defEqCtx_x3f_160_ = lean_ctor_get(v_a_119_, 4);
v_synthPendingDepth_161_ = lean_ctor_get(v_a_119_, 5);
v_customCanUnfoldPredicate_x3f_162_ = lean_ctor_get(v_a_119_, 6);
v_univApprox_163_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_164_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 2);
v_cacheInferType_165_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_155_);
v___x_166_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_153_, v_keyedConfig_155_);
lean_inc(v_customCanUnfoldPredicate_x3f_162_);
lean_inc(v_synthPendingDepth_161_);
lean_inc(v_defEqCtx_x3f_160_);
lean_inc_ref(v_localInstances_159_);
lean_inc_ref(v_lctx_158_);
lean_inc(v_zetaDeltaSet_157_);
v___x_167_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_zetaDeltaSet_157_);
lean_ctor_set(v___x_167_, 2, v_lctx_158_);
lean_ctor_set(v___x_167_, 3, v_localInstances_159_);
lean_ctor_set(v___x_167_, 4, v_defEqCtx_x3f_160_);
lean_ctor_set(v___x_167_, 5, v_synthPendingDepth_161_);
lean_ctor_set(v___x_167_, 6, v_customCanUnfoldPredicate_x3f_162_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*7, v_trackZetaDelta_156_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*7 + 1, v_univApprox_163_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*7 + 2, v_inTypeClassResolution_164_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*7 + 3, v_cacheInferType_165_);
v___x_168_ = l_Lean_Meta_isExprDefEq(v_e1_117_, v_e2_118_, v___x_167_, v_a_120_, v___y_144_, v___y_143_);
lean_dec_ref(v___y_144_);
lean_dec_ref_known(v___x_167_, 7);
v___y_125_ = v___x_168_;
goto v___jp_124_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_isExprDefEq(v_e1_117_, v_e2_118_, v_a_119_, v_a_120_, v___y_144_, v___y_143_);
lean_dec_ref(v___y_144_);
v___y_125_ = v___x_169_;
goto v___jp_124_;
}
}
else
{
lean_object* v___x_171_; 
lean_dec_ref(v___y_144_);
lean_dec_ref(v_e2_118_);
lean_dec_ref(v_e1_117_);
if (v_isShared_149_ == 0)
{
v___x_171_ = v___x_148_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_146_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v___y_144_);
lean_dec_ref(v_e2_118_);
lean_dec_ref(v_e1_117_);
v_a_174_ = lean_ctor_get(v___y_145_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___y_145_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___y_145_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___y_145_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
v___jp_199_:
{
lean_object* v___x_217_; uint8_t v_transparency_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_217_ = l_Lean_Meta_Context_config(v_a_119_);
v_transparency_218_ = lean_ctor_get_uint8(v___x_217_, 9);
lean_dec_ref(v___x_217_);
v___x_219_ = l_Lean_maxRecDepth;
v___x_220_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v___y_200_, v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_221_, 0, v_fileName_202_);
lean_ctor_set(v___x_221_, 1, v_fileMap_203_);
lean_ctor_set(v___x_221_, 2, v___y_200_);
lean_ctor_set(v___x_221_, 3, v___x_220_);
lean_ctor_set(v___x_221_, 4, v_currNamespace_204_);
lean_ctor_set(v___x_221_, 5, v_openDecls_205_);
lean_ctor_set(v___x_221_, 6, v_initHeartbeats_206_);
lean_ctor_set(v___x_221_, 7, v_maxHeartbeats_207_);
lean_ctor_set(v___x_221_, 8, v_quotContext_208_);
lean_ctor_set(v___x_221_, 9, v_currMacroScope_209_);
lean_ctor_set(v___x_221_, 10, v_cancelTk_x3f_210_);
lean_ctor_set(v___x_221_, 11, v_inheritedTraceOptions_211_);
lean_inc(v_ref_213_);
lean_inc(v_currRecDepth_212_);
v___x_222_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_currRecDepth_212_);
lean_ctor_set(v___x_222_, 2, v_ref_213_);
lean_ctor_set_uint16(v___x_222_, sizeof(void*)*3, v___y_201_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*3 + 2, v_suppressElabErrors_214_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*3 + 3, v_isRecordingDeps_215_);
v___x_223_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_218_, v___x_198_);
if (v___x_223_ == 0)
{
lean_object* v_keyedConfig_224_; uint8_t v_trackZetaDelta_225_; lean_object* v_zetaDeltaSet_226_; lean_object* v_lctx_227_; lean_object* v_localInstances_228_; lean_object* v_defEqCtx_x3f_229_; lean_object* v_synthPendingDepth_230_; lean_object* v_customCanUnfoldPredicate_x3f_231_; uint8_t v_univApprox_232_; uint8_t v_inTypeClassResolution_233_; uint8_t v_cacheInferType_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_keyedConfig_224_ = lean_ctor_get(v_a_119_, 0);
v_trackZetaDelta_225_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7);
v_zetaDeltaSet_226_ = lean_ctor_get(v_a_119_, 1);
v_lctx_227_ = lean_ctor_get(v_a_119_, 2);
v_localInstances_228_ = lean_ctor_get(v_a_119_, 3);
v_defEqCtx_x3f_229_ = lean_ctor_get(v_a_119_, 4);
v_synthPendingDepth_230_ = lean_ctor_get(v_a_119_, 5);
v_customCanUnfoldPredicate_x3f_231_ = lean_ctor_get(v_a_119_, 6);
v_univApprox_232_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_233_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 2);
v_cacheInferType_234_ = lean_ctor_get_uint8(v_a_119_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_224_);
v___x_235_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_198_, v_keyedConfig_224_);
lean_inc(v_customCanUnfoldPredicate_x3f_231_);
lean_inc(v_synthPendingDepth_230_);
lean_inc(v_defEqCtx_x3f_229_);
lean_inc_ref(v_localInstances_228_);
lean_inc_ref(v_lctx_227_);
lean_inc(v_zetaDeltaSet_226_);
v___x_236_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_zetaDeltaSet_226_);
lean_ctor_set(v___x_236_, 2, v_lctx_227_);
lean_ctor_set(v___x_236_, 3, v_localInstances_228_);
lean_ctor_set(v___x_236_, 4, v_defEqCtx_x3f_229_);
lean_ctor_set(v___x_236_, 5, v_synthPendingDepth_230_);
lean_ctor_set(v___x_236_, 6, v_customCanUnfoldPredicate_x3f_231_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*7, v_trackZetaDelta_225_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*7 + 1, v_univApprox_232_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*7 + 2, v_inTypeClassResolution_233_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*7 + 3, v_cacheInferType_234_);
lean_inc_ref(v_e2_118_);
lean_inc_ref(v_e1_117_);
v___x_237_ = l_Lean_Meta_isExprDefEq(v_e1_117_, v_e2_118_, v___x_236_, v_a_120_, v___x_222_, v___y_216_);
lean_dec_ref_known(v___x_236_, 7);
v___y_143_ = v___y_216_;
v___y_144_ = v___x_222_;
v___y_145_ = v___x_237_;
goto v___jp_142_;
}
else
{
lean_object* v___x_238_; 
lean_inc_ref(v_e2_118_);
lean_inc_ref(v_e1_117_);
v___x_238_ = l_Lean_Meta_isExprDefEq(v_e1_117_, v_e2_118_, v_a_119_, v_a_120_, v___x_222_, v___y_216_);
v___y_143_ = v___y_216_;
v___y_144_ = v___x_222_;
v___y_145_ = v___x_238_;
goto v___jp_142_;
}
}
v___jp_239_:
{
lean_object* v___x_243_; lean_object* v_env_244_; lean_object* v_nextMacroScope_245_; lean_object* v_ngen_246_; lean_object* v_auxDeclNGen_247_; lean_object* v_traceState_248_; lean_object* v_recordedDeps_249_; lean_object* v_messages_250_; lean_object* v_infoState_251_; lean_object* v_snapshotTasks_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v___x_243_ = lean_st_ref_take(v_a_122_);
v_env_244_ = lean_ctor_get(v___x_243_, 0);
v_nextMacroScope_245_ = lean_ctor_get(v___x_243_, 1);
v_ngen_246_ = lean_ctor_get(v___x_243_, 2);
v_auxDeclNGen_247_ = lean_ctor_get(v___x_243_, 3);
v_traceState_248_ = lean_ctor_get(v___x_243_, 4);
v_recordedDeps_249_ = lean_ctor_get(v___x_243_, 6);
v_messages_250_ = lean_ctor_get(v___x_243_, 7);
v_infoState_251_ = lean_ctor_get(v___x_243_, 8);
v_snapshotTasks_252_ = lean_ctor_get(v___x_243_, 9);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_243_, 5);
lean_dec(v_unused_263_);
v___x_254_ = v___x_243_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snapshotTasks_252_);
lean_inc(v_infoState_251_);
lean_inc(v_messages_250_);
lean_inc(v_recordedDeps_249_);
lean_inc(v_traceState_248_);
lean_inc(v_auxDeclNGen_247_);
lean_inc(v_ngen_246_);
lean_inc(v_nextMacroScope_245_);
lean_inc(v_env_244_);
lean_dec(v___x_243_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = l_Lean_Kernel_enableDiag(v_env_244_, v___y_240_);
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
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_nextMacroScope_245_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_ngen_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_auxDeclNGen_247_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_traceState_248_);
lean_ctor_set(v_reuseFailAlloc_261_, 5, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 6, v_recordedDeps_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 7, v_messages_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 8, v_infoState_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 9, v_snapshotTasks_252_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_st_ref_put(v_a_122_, v___x_259_);
lean_inc_ref(v_inheritedTraceOptions_197_);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_currMacroScope_195_);
lean_inc(v_quotContext_194_);
lean_inc(v_maxHeartbeats_193_);
lean_inc(v_initHeartbeats_192_);
lean_inc(v_openDecls_191_);
lean_inc(v_currNamespace_190_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___y_200_ = v___y_241_;
v___y_201_ = v___y_242_;
v_fileName_202_ = v_fileName_187_;
v_fileMap_203_ = v_fileMap_188_;
v_currNamespace_204_ = v_currNamespace_190_;
v_openDecls_205_ = v_openDecls_191_;
v_initHeartbeats_206_ = v_initHeartbeats_192_;
v_maxHeartbeats_207_ = v_maxHeartbeats_193_;
v_quotContext_208_ = v_quotContext_194_;
v_currMacroScope_209_ = v_currMacroScope_195_;
v_cancelTk_x3f_210_ = v_cancelTk_x3f_196_;
v_inheritedTraceOptions_211_ = v_inheritedTraceOptions_197_;
v_currRecDepth_212_ = v_currRecDepth_183_;
v_ref_213_ = v_ref_184_;
v_suppressElabErrors_214_ = v_suppressElabErrors_185_;
v_isRecordingDeps_215_ = v_isRecordingDeps_186_;
v___y_216_ = v_a_122_;
goto v___jp_199_;
}
}
}
v___jp_264_:
{
uint16_t v___x_266_; lean_object* v___x_267_; lean_object* v_env_268_; uint8_t v___x_269_; uint16_t v___x_270_; uint16_t v___x_271_; uint16_t v___x_272_; uint8_t v___x_273_; 
v___x_266_ = l_Lean_OptionFlags_ofOptions(v___y_265_);
v___x_267_ = lean_st_ref_get(v_a_122_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_268_);
lean_dec_ref(v_env_268_);
v___x_270_ = 512;
v___x_271_ = lean_uint16_land(v___x_266_, v___x_270_);
v___x_272_ = 0;
v___x_273_ = lean_uint16_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
if (v___x_269_ == 0)
{
uint8_t v___x_274_; 
v___x_274_ = 1;
v___y_240_ = v___x_274_;
v___y_241_ = v___y_265_;
v___y_242_ = v___x_266_;
goto v___jp_239_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_197_);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_currMacroScope_195_);
lean_inc(v_quotContext_194_);
lean_inc(v_maxHeartbeats_193_);
lean_inc(v_initHeartbeats_192_);
lean_inc(v_openDecls_191_);
lean_inc(v_currNamespace_190_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___y_200_ = v___y_265_;
v___y_201_ = v___x_266_;
v_fileName_202_ = v_fileName_187_;
v_fileMap_203_ = v_fileMap_188_;
v_currNamespace_204_ = v_currNamespace_190_;
v_openDecls_205_ = v_openDecls_191_;
v_initHeartbeats_206_ = v_initHeartbeats_192_;
v_maxHeartbeats_207_ = v_maxHeartbeats_193_;
v_quotContext_208_ = v_quotContext_194_;
v_currMacroScope_209_ = v_currMacroScope_195_;
v_cancelTk_x3f_210_ = v_cancelTk_x3f_196_;
v_inheritedTraceOptions_211_ = v_inheritedTraceOptions_197_;
v_currRecDepth_212_ = v_currRecDepth_183_;
v_ref_213_ = v_ref_184_;
v_suppressElabErrors_214_ = v_suppressElabErrors_185_;
v_isRecordingDeps_215_ = v_isRecordingDeps_186_;
v___y_216_ = v_a_122_;
goto v___jp_199_;
}
}
else
{
if (v___x_269_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_197_);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_currMacroScope_195_);
lean_inc(v_quotContext_194_);
lean_inc(v_maxHeartbeats_193_);
lean_inc(v_initHeartbeats_192_);
lean_inc(v_openDecls_191_);
lean_inc(v_currNamespace_190_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___y_200_ = v___y_265_;
v___y_201_ = v___x_266_;
v_fileName_202_ = v_fileName_187_;
v_fileMap_203_ = v_fileMap_188_;
v_currNamespace_204_ = v_currNamespace_190_;
v_openDecls_205_ = v_openDecls_191_;
v_initHeartbeats_206_ = v_initHeartbeats_192_;
v_maxHeartbeats_207_ = v_maxHeartbeats_193_;
v_quotContext_208_ = v_quotContext_194_;
v_currMacroScope_209_ = v_currMacroScope_195_;
v_cancelTk_x3f_210_ = v_cancelTk_x3f_196_;
v_inheritedTraceOptions_211_ = v_inheritedTraceOptions_197_;
v_currRecDepth_212_ = v_currRecDepth_183_;
v_ref_213_ = v_ref_184_;
v_suppressElabErrors_214_ = v_suppressElabErrors_185_;
v_isRecordingDeps_215_ = v_isRecordingDeps_186_;
v___y_216_ = v_a_122_;
goto v___jp_199_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = 0;
v___y_240_ = v___x_275_;
v___y_241_ = v___y_265_;
v___y_242_ = v___x_266_;
goto v___jp_239_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_0interp(lean_interpreter_value* stack)
{
lean_object* v_e1_117_ = stack[0].m_obj;
lean_object* v_e2_118_ = stack[1].m_obj;
lean_object* v_a_119_ = stack[2].m_obj;
lean_object* v_a_120_ = stack[3].m_obj;
lean_object* v_a_121_ = stack[4].m_obj;
lean_object* v_a_122_ = stack[5].m_obj;
lean_object* v_res_279_;
v_res_279_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_e1_117_, v_e2_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(lean_object* v_e1_280_, lean_object* v_e2_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_e1_280_, v_e2_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_287_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(lean_object* v_k_288_, lean_object* v_b_289_, lean_object* v_c_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
lean_inc(v___y_294_);
lean_inc_ref(v___y_293_);
lean_inc(v___y_292_);
lean_inc_ref(v___y_291_);
v___x_296_ = lean_apply_7(v_k_288_, v_b_289_, v_c_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, lean_box(0));
return v___x_296_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_288_ = stack[0].m_obj;
lean_object* v_b_289_ = stack[1].m_obj;
lean_object* v_c_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v___y_293_ = stack[5].m_obj;
lean_object* v___y_294_ = stack[6].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_288_, v_b_289_, v_c_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(lean_object* v_k_298_, lean_object* v_b_299_, lean_object* v_c_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_298_, v_b_299_, v_c_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(lean_object* v_type_307_, lean_object* v_k_308_, uint8_t v_cleanupAnnotations_309_, uint8_t v_whnfType_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; 
v___f_316_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_316_, 0, v_k_308_);
v___x_317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_307_, v___f_316_, v_cleanupAnnotations_309_, v_whnfType_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_317_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_307_ = stack[0].m_obj;
lean_object* v_k_308_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_309_ = stack[2].m_num;
uint8_t v_whnfType_310_ = stack[3].m_num;
lean_object* v___y_311_ = stack[4].m_obj;
lean_object* v___y_312_ = stack[5].m_obj;
lean_object* v___y_313_ = stack[6].m_obj;
lean_object* v___y_314_ = stack[7].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_307_, v_k_308_, v_cleanupAnnotations_309_, v_whnfType_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(lean_object* v_type_335_, lean_object* v_k_336_, lean_object* v_cleanupAnnotations_337_, lean_object* v_whnfType_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_344_; uint8_t v_whnfType_boxed_345_; lean_object* v_res_346_; 
v_cleanupAnnotations_boxed_344_ = lean_unbox(v_cleanupAnnotations_337_);
v_whnfType_boxed_345_ = lean_unbox(v_whnfType_338_);
v_res_346_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_335_, v_k_336_, v_cleanupAnnotations_boxed_344_, v_whnfType_boxed_345_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_346_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_object* v_00_u03b1_347_, lean_object* v_type_348_, lean_object* v_k_349_, uint8_t v_cleanupAnnotations_350_, uint8_t v_whnfType_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_348_, v_k_349_, v_cleanupAnnotations_350_, v_whnfType_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_348_ = stack[1].m_obj;
lean_object* v_k_349_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_350_ = stack[3].m_num;
uint8_t v_whnfType_351_ = stack[4].m_num;
lean_object* v___y_352_ = stack[5].m_obj;
lean_object* v___y_353_ = stack[6].m_obj;
lean_object* v___y_354_ = stack[7].m_obj;
lean_object* v___y_355_ = stack[8].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(lean_box(0), v_type_348_, v_k_349_, v_cleanupAnnotations_350_, v_whnfType_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(lean_object* v_00_u03b1_359_, lean_object* v_type_360_, lean_object* v_k_361_, lean_object* v_cleanupAnnotations_362_, lean_object* v_whnfType_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_369_; uint8_t v_whnfType_boxed_370_; lean_object* v_res_371_; 
v_cleanupAnnotations_boxed_369_ = lean_unbox(v_cleanupAnnotations_362_);
v_whnfType_boxed_370_ = lean_unbox(v_whnfType_363_);
v_res_371_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(v_00_u03b1_359_, v_type_360_, v_k_361_, v_cleanupAnnotations_boxed_369_, v_whnfType_boxed_370_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_371_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(lean_object* v_msgData_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; lean_object* v_env_379_; uint8_t v___x_380_; lean_object* v_env_381_; lean_object* v___x_382_; lean_object* v_toCold_383_; lean_object* v_mctx_384_; lean_object* v_lctx_385_; lean_object* v_options_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_378_ = lean_st_ref_get(v___y_376_);
v_env_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc_ref(v_env_379_);
lean_dec(v___x_378_);
v___x_380_ = 0;
v_env_381_ = l_Lean_Environment_setRecordingDeps(v_env_379_, v___x_380_);
v___x_382_ = lean_st_ref_get(v___y_374_);
v_toCold_383_ = lean_ctor_get(v___y_375_, 0);
v_mctx_384_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_mctx_384_);
lean_dec(v___x_382_);
v_lctx_385_ = lean_ctor_get(v___y_373_, 2);
v_options_386_ = lean_ctor_get(v_toCold_383_, 2);
lean_inc_ref(v_options_386_);
lean_inc_ref(v_lctx_385_);
v___x_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_387_, 0, v_env_381_);
lean_ctor_set(v___x_387_, 1, v_mctx_384_);
lean_ctor_set(v___x_387_, 2, v_lctx_385_);
lean_ctor_set(v___x_387_, 3, v_options_386_);
v___x_388_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_msgData_372_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_372_ = stack[0].m_obj;
lean_object* v___y_373_ = stack[1].m_obj;
lean_object* v___y_374_ = stack[2].m_obj;
lean_object* v___y_375_ = stack[3].m_obj;
lean_object* v___y_376_ = stack[4].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(lean_object* v_msgData_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
v_ref_404_ = lean_ctor_get(v___y_401_, 2);
v___x_405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_414_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_inc(v_ref_404_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_ref_404_);
lean_ctor_set(v___x_410_, 1, v_a_406_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_398_ = stack[0].m_obj;
lean_object* v___y_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v___y_402_ = stack[4].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(lean_object* v_k_429_, lean_object* v_x_430_, lean_object* v_type_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
v___x_437_ = lean_whnf(v_type_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_440_ = lean_unsigned_to_nat(3u);
v___x_441_ = l_Lean_Expr_isAppOfArity(v_a_438_, v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v_k_429_);
v___x_442_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3, &l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once, _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3);
v___x_443_ = lean_unsigned_to_nat(30u);
v___x_444_ = l_Lean_inlineExpr(v_a_438_, v___x_443_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_442_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_445_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = l_Lean_Expr_appFn_x21(v_a_438_);
v___x_448_ = l_Lean_Expr_appArg_x21(v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = l_Lean_Expr_appArg_x21(v_a_438_);
lean_dec(v_a_438_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
v___x_450_ = lean_apply_7(v_k_429_, v___x_448_, v___x_449_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, lean_box(0));
return v___x_450_;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_k_429_);
v_a_451_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_437_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_437_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_429_ = stack[0].m_obj;
lean_object* v_x_430_ = stack[1].m_obj;
lean_object* v_type_431_ = stack[2].m_obj;
lean_object* v___y_432_ = stack[3].m_obj;
lean_object* v___y_433_ = stack[4].m_obj;
lean_object* v___y_434_ = stack[5].m_obj;
lean_object* v___y_435_ = stack[6].m_obj;
lean_object* v_res_459_;
v_res_459_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(v_k_429_, v_x_430_, v_type_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(lean_object* v_k_460_, lean_object* v_x_461_, lean_object* v_type_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(v_k_460_, v_x_461_, v_type_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_x_461_);
return v_res_468_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(lean_object* v_type_469_, lean_object* v_k_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___y_477_; lean_object* v___x_494_; uint8_t v_transparency_495_; lean_object* v___f_496_; uint8_t v___x_497_; uint8_t v___x_498_; uint8_t v___x_499_; 
v___x_494_ = l_Lean_Meta_Context_config(v_a_471_);
v_transparency_495_ = lean_ctor_get_uint8(v___x_494_, 9);
lean_dec_ref(v___x_494_);
v___f_496_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_496_, 0, v_k_470_);
v___x_497_ = 0;
v___x_498_ = 0;
v___x_499_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_495_, v___x_497_);
if (v___x_499_ == 0)
{
lean_object* v_keyedConfig_500_; uint8_t v_trackZetaDelta_501_; lean_object* v_zetaDeltaSet_502_; lean_object* v_lctx_503_; lean_object* v_localInstances_504_; lean_object* v_defEqCtx_x3f_505_; lean_object* v_synthPendingDepth_506_; lean_object* v_customCanUnfoldPredicate_x3f_507_; uint8_t v_univApprox_508_; uint8_t v_inTypeClassResolution_509_; uint8_t v_cacheInferType_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_keyedConfig_500_ = lean_ctor_get(v_a_471_, 0);
v_trackZetaDelta_501_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7);
v_zetaDeltaSet_502_ = lean_ctor_get(v_a_471_, 1);
v_lctx_503_ = lean_ctor_get(v_a_471_, 2);
v_localInstances_504_ = lean_ctor_get(v_a_471_, 3);
v_defEqCtx_x3f_505_ = lean_ctor_get(v_a_471_, 4);
v_synthPendingDepth_506_ = lean_ctor_get(v_a_471_, 5);
v_customCanUnfoldPredicate_x3f_507_ = lean_ctor_get(v_a_471_, 6);
v_univApprox_508_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_509_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 2);
v_cacheInferType_510_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_500_);
v___x_511_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_497_, v_keyedConfig_500_);
lean_inc(v_customCanUnfoldPredicate_x3f_507_);
lean_inc(v_synthPendingDepth_506_);
lean_inc(v_defEqCtx_x3f_505_);
lean_inc_ref(v_localInstances_504_);
lean_inc_ref(v_lctx_503_);
lean_inc(v_zetaDeltaSet_502_);
v___x_512_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_zetaDeltaSet_502_);
lean_ctor_set(v___x_512_, 2, v_lctx_503_);
lean_ctor_set(v___x_512_, 3, v_localInstances_504_);
lean_ctor_set(v___x_512_, 4, v_defEqCtx_x3f_505_);
lean_ctor_set(v___x_512_, 5, v_synthPendingDepth_506_);
lean_ctor_set(v___x_512_, 6, v_customCanUnfoldPredicate_x3f_507_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*7, v_trackZetaDelta_501_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*7 + 1, v_univApprox_508_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*7 + 2, v_inTypeClassResolution_509_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*7 + 3, v_cacheInferType_510_);
v___x_513_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_469_, v___f_496_, v___x_498_, v___x_498_, v___x_512_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref_known(v___x_512_, 7);
v___y_477_ = v___x_513_;
goto v___jp_476_;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_469_, v___f_496_, v___x_498_, v___x_498_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
v___y_477_ = v___x_514_;
goto v___jp_476_;
}
v___jp_476_:
{
if (lean_obj_tag(v___y_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___y_477_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___y_477_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___y_477_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___y_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___y_477_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___y_477_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___y_477_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___y_477_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_469_ = stack[0].m_obj;
lean_object* v_k_470_ = stack[1].m_obj;
lean_object* v_a_471_ = stack[2].m_obj;
lean_object* v_a_472_ = stack[3].m_obj;
lean_object* v_a_473_ = stack[4].m_obj;
lean_object* v_a_474_ = stack[5].m_obj;
lean_object* v_res_515_;
v_res_515_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_469_, v_k_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(lean_object* v_type_516_, lean_object* v_k_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_516_, v_k_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_523_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_object* v_00_u03b1_524_, lean_object* v_type_525_, lean_object* v_k_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_525_, v_k_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_532_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_525_ = stack[1].m_obj;
lean_object* v_k_526_ = stack[2].m_obj;
lean_object* v_a_527_ = stack[3].m_obj;
lean_object* v_a_528_ = stack[4].m_obj;
lean_object* v_a_529_ = stack[5].m_obj;
lean_object* v_a_530_ = stack[6].m_obj;
lean_object* v_res_533_;
v_res_533_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(lean_box(0), v_type_525_, v_k_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(lean_object* v_00_u03b1_534_, lean_object* v_type_535_, lean_object* v_k_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(v_00_u03b1_534_, v_type_535_, v_k_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
return v_res_542_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_object* v_00_u03b1_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_544_ = stack[1].m_obj;
lean_object* v___y_545_ = stack[2].m_obj;
lean_object* v___y_546_ = stack[3].m_obj;
lean_object* v___y_547_ = stack[4].m_obj;
lean_object* v___y_548_ = stack[5].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(lean_box(0), v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(lean_object* v_00_u03b1_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(v_00_u03b1_552_, v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(lean_object* v___y_560_, uint8_t v_isExporting_561_, lean_object* v___x_562_, lean_object* v___y_563_, lean_object* v___x_564_, lean_object* v_a_x3f_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_env_568_; lean_object* v_nextMacroScope_569_; lean_object* v_ngen_570_; lean_object* v_auxDeclNGen_571_; lean_object* v_traceState_572_; lean_object* v_recordedDeps_573_; lean_object* v_messages_574_; lean_object* v_infoState_575_; lean_object* v_snapshotTasks_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_601_; 
v___x_567_ = lean_st_ref_take(v___y_560_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
v_nextMacroScope_569_ = lean_ctor_get(v___x_567_, 1);
v_ngen_570_ = lean_ctor_get(v___x_567_, 2);
v_auxDeclNGen_571_ = lean_ctor_get(v___x_567_, 3);
v_traceState_572_ = lean_ctor_get(v___x_567_, 4);
v_recordedDeps_573_ = lean_ctor_get(v___x_567_, 6);
v_messages_574_ = lean_ctor_get(v___x_567_, 7);
v_infoState_575_ = lean_ctor_get(v___x_567_, 8);
v_snapshotTasks_576_ = lean_ctor_get(v___x_567_, 9);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_567_, 5);
lean_dec(v_unused_602_);
v___x_578_ = v___x_567_;
v_isShared_579_ = v_isSharedCheck_601_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snapshotTasks_576_);
lean_inc(v_infoState_575_);
lean_inc(v_messages_574_);
lean_inc(v_recordedDeps_573_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_571_);
lean_inc(v_ngen_570_);
lean_inc(v_nextMacroScope_569_);
lean_inc(v_env_568_);
lean_dec(v___x_567_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_601_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = l_Lean_Environment_setExporting(v_env_568_, v_isExporting_561_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 5, v___x_562_);
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_nextMacroScope_569_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_ngen_570_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_auxDeclNGen_571_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_traceState_572_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_recordedDeps_573_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_messages_574_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_infoState_575_);
lean_ctor_set(v_reuseFailAlloc_600_, 9, v_snapshotTasks_576_);
v___x_582_ = v_reuseFailAlloc_600_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_mctx_585_; lean_object* v_zetaDeltaFVarIds_586_; lean_object* v_postponed_587_; lean_object* v_diag_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_598_; 
v___x_583_ = lean_st_ref_put(v___y_560_, v___x_582_);
v___x_584_ = lean_st_ref_take(v___y_563_);
v_mctx_585_ = lean_ctor_get(v___x_584_, 0);
v_zetaDeltaFVarIds_586_ = lean_ctor_get(v___x_584_, 2);
v_postponed_587_ = lean_ctor_get(v___x_584_, 3);
v_diag_588_ = lean_ctor_get(v___x_584_, 4);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_599_);
v___x_590_ = v___x_584_;
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_diag_588_);
lean_inc(v_postponed_587_);
lean_inc(v_zetaDeltaFVarIds_586_);
lean_inc(v_mctx_585_);
lean_dec(v___x_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_598_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_564_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_mctx_585_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_zetaDeltaFVarIds_586_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_postponed_587_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_diag_588_);
v___x_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_st_ref_put(v___y_563_, v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_592_);
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_560_ = stack[0].m_obj;
uint8_t v_isExporting_561_ = stack[1].m_num;
lean_object* v___x_562_ = stack[2].m_obj;
lean_object* v___y_563_ = stack[3].m_obj;
lean_object* v___x_564_ = stack[4].m_obj;
lean_object* v_a_x3f_565_ = stack[5].m_obj;
lean_object* v_res_603_;
v_res_603_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_560_, v_isExporting_561_, v___x_562_, v___y_563_, v___x_564_, v_a_x3f_565_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___y_604_, lean_object* v_isExporting_605_, lean_object* v___x_606_, lean_object* v___y_607_, lean_object* v___x_608_, lean_object* v_a_x3f_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_isExporting_boxed_611_; lean_object* v_res_612_; 
v_isExporting_boxed_611_ = lean_unbox(v_isExporting_605_);
v_res_612_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_604_, v_isExporting_boxed_611_, v___x_606_, v___y_607_, v___x_608_, v_a_x3f_609_);
lean_dec(v_a_x3f_609_);
lean_dec(v___y_607_);
lean_dec(v___y_604_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
v___x_614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
lean_ctor_set(v___x_614_, 2, v___x_613_);
lean_ctor_set(v___x_614_, 3, v___x_613_);
lean_ctor_set(v___x_614_, 4, v___x_613_);
lean_ctor_set(v___x_614_, 5, v___x_613_);
return v___x_614_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(lean_object* v_x_615_, uint8_t v_isExporting_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_env_623_; lean_object* v___x_624_; uint8_t v_isModule_625_; 
v___x_622_ = lean_st_ref_get(v___y_620_);
v_env_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_622_);
v___x_624_ = l_Lean_Environment_header(v_env_623_);
v_isModule_625_ = lean_ctor_get_uint8(v___x_624_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_624_);
if (v_isModule_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_env_623_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
v___x_626_ = lean_apply_5(v_x_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
return v___x_626_;
}
else
{
uint8_t v_isExporting_627_; 
v_isExporting_627_ = lean_ctor_get_uint8(v_env_623_, sizeof(void*)*13);
lean_dec_ref(v_env_623_);
if (v_isExporting_616_ == 0)
{
if (v_isExporting_627_ == 0)
{
lean_object* v___x_694_; 
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
v___x_694_ = lean_apply_5(v_x_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
return v___x_694_;
}
else
{
goto v___jp_628_;
}
}
else
{
if (v_isExporting_627_ == 0)
{
goto v___jp_628_;
}
else
{
lean_object* v___x_695_; 
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
v___x_695_ = lean_apply_5(v_x_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
return v___x_695_;
}
}
v___jp_628_:
{
lean_object* v___x_629_; lean_object* v_env_630_; lean_object* v_nextMacroScope_631_; lean_object* v_ngen_632_; lean_object* v_auxDeclNGen_633_; lean_object* v_traceState_634_; lean_object* v_recordedDeps_635_; lean_object* v_messages_636_; lean_object* v_infoState_637_; lean_object* v_snapshotTasks_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_692_; 
v___x_629_ = lean_st_ref_take(v___y_620_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
v_nextMacroScope_631_ = lean_ctor_get(v___x_629_, 1);
v_ngen_632_ = lean_ctor_get(v___x_629_, 2);
v_auxDeclNGen_633_ = lean_ctor_get(v___x_629_, 3);
v_traceState_634_ = lean_ctor_get(v___x_629_, 4);
v_recordedDeps_635_ = lean_ctor_get(v___x_629_, 6);
v_messages_636_ = lean_ctor_get(v___x_629_, 7);
v_infoState_637_ = lean_ctor_get(v___x_629_, 8);
v_snapshotTasks_638_ = lean_ctor_get(v___x_629_, 9);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_629_, 5);
lean_dec(v_unused_693_);
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_692_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snapshotTasks_638_);
lean_inc(v_infoState_637_);
lean_inc(v_messages_636_);
lean_inc(v_recordedDeps_635_);
lean_inc(v_traceState_634_);
lean_inc(v_auxDeclNGen_633_);
lean_inc(v_ngen_632_);
lean_inc(v_nextMacroScope_631_);
lean_inc(v_env_630_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_692_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = l_Lean_Environment_setExporting(v_env_630_, v_isExporting_616_);
v___x_643_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 5, v___x_643_);
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_nextMacroScope_631_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_ngen_632_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_auxDeclNGen_633_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_traceState_634_);
lean_ctor_set(v_reuseFailAlloc_691_, 5, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_691_, 6, v_recordedDeps_635_);
lean_ctor_set(v_reuseFailAlloc_691_, 7, v_messages_636_);
lean_ctor_set(v_reuseFailAlloc_691_, 8, v_infoState_637_);
lean_ctor_set(v_reuseFailAlloc_691_, 9, v_snapshotTasks_638_);
v___x_645_ = v_reuseFailAlloc_691_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_mctx_648_; lean_object* v_zetaDeltaFVarIds_649_; lean_object* v_postponed_650_; lean_object* v_diag_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_689_; 
v___x_646_ = lean_st_ref_put(v___y_620_, v___x_645_);
v___x_647_ = lean_st_ref_take(v___y_618_);
v_mctx_648_ = lean_ctor_get(v___x_647_, 0);
v_zetaDeltaFVarIds_649_ = lean_ctor_get(v___x_647_, 2);
v_postponed_650_ = lean_ctor_get(v___x_647_, 3);
v_diag_651_ = lean_ctor_get(v___x_647_, 4);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_647_, 1);
lean_dec(v_unused_690_);
v___x_653_ = v___x_647_;
v_isShared_654_ = v_isSharedCheck_689_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_diag_651_);
lean_inc(v_postponed_650_);
lean_inc(v_zetaDeltaFVarIds_649_);
lean_inc(v_mctx_648_);
lean_dec(v___x_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_689_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_mctx_648_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_zetaDeltaFVarIds_649_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_postponed_650_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_diag_651_);
v___x_657_ = v_reuseFailAlloc_688_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v_r_659_; 
v___x_658_ = lean_st_ref_put(v___y_618_, v___x_657_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
v_r_659_ = lean_apply_5(v_x_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
if (lean_obj_tag(v_r_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_676_; 
v_a_660_ = lean_ctor_get(v_r_659_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_r_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_662_ = v_r_659_;
v_isShared_663_ = v_isSharedCheck_676_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v_r_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_676_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
lean_inc(v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_675_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v___x_666_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_620_, v_isExporting_627_, v___x_643_, v___y_618_, v___x_655_, v___x_665_);
lean_dec_ref(v___x_665_);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_674_);
v___x_668_ = v___x_666_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_dec(v___x_666_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_a_660_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_660_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_677_ = lean_ctor_get(v_r_659_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v_r_659_, 1);
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_620_, v_isExporting_627_, v___x_643_, v___y_618_, v___x_655_, v___x_678_);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_679_, 0);
lean_dec(v_unused_687_);
v___x_681_ = v___x_679_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_dec(v___x_679_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 1);
lean_ctor_set(v___x_681_, 0, v_a_677_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_677_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_615_ = stack[0].m_obj;
uint8_t v_isExporting_616_ = stack[1].m_num;
lean_object* v___y_617_ = stack[2].m_obj;
lean_object* v___y_618_ = stack[3].m_obj;
lean_object* v___y_619_ = stack[4].m_obj;
lean_object* v___y_620_ = stack[5].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_615_, v_isExporting_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_697_, lean_object* v_isExporting_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
uint8_t v_isExporting_boxed_704_; lean_object* v_res_705_; 
v_isExporting_boxed_704_ = lean_unbox(v_isExporting_698_);
v_res_705_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_697_, v_isExporting_boxed_704_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_705_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(lean_object* v_x_706_, uint8_t v_when_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
if (v_when_707_ == 0)
{
lean_object* v___x_713_; 
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
v___x_713_ = lean_apply_5(v_x_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, lean_box(0));
return v___x_713_;
}
else
{
uint8_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 0;
v___x_715_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_706_, v___x_714_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
return v___x_715_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_706_ = stack[0].m_obj;
uint8_t v_when_707_ = stack[1].m_num;
lean_object* v___y_708_ = stack[2].m_obj;
lean_object* v___y_709_ = stack[3].m_obj;
lean_object* v___y_710_ = stack[4].m_obj;
lean_object* v___y_711_ = stack[5].m_obj;
lean_object* v_res_716_;
v_res_716_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_706_, v_when_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
stack->m_obj
 = v_res_716_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(lean_object* v_x_717_, lean_object* v_when_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_when_boxed_724_; lean_object* v_res_725_; 
v_when_boxed_724_ = lean_unbox(v_when_718_);
v_res_725_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_717_, v_when_boxed_724_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_725_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__0));
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__2));
v___x_731_ = l_Lean_stringToMessageData(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_validateDefEqAttr___lam__0___closed__4));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__5, &l_Lean_validateDefEqAttr___lam__0___closed__5_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__5);
v___x_736_ = l_Lean_MessageData_note(v___x_735_);
return v___x_736_;
}
}
lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* v___x_737_, lean_object* v_lhs_738_, lean_object* v_rhs_739_, uint8_t v___x_740_, uint8_t v_a_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_toCold_747_; uint8_t v_trackZetaDelta_748_; lean_object* v_zetaDeltaSet_749_; lean_object* v_lctx_750_; lean_object* v_localInstances_751_; lean_object* v_defEqCtx_x3f_752_; lean_object* v_synthPendingDepth_753_; lean_object* v_customCanUnfoldPredicate_x3f_754_; uint8_t v_univApprox_755_; uint8_t v_inTypeClassResolution_756_; uint8_t v_cacheInferType_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_907_; 
v_toCold_747_ = lean_ctor_get(v___y_744_, 0);
lean_inc_ref(v_toCold_747_);
v_trackZetaDelta_748_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*7);
v_zetaDeltaSet_749_ = lean_ctor_get(v___y_742_, 1);
v_lctx_750_ = lean_ctor_get(v___y_742_, 2);
v_localInstances_751_ = lean_ctor_get(v___y_742_, 3);
v_defEqCtx_x3f_752_ = lean_ctor_get(v___y_742_, 4);
v_synthPendingDepth_753_ = lean_ctor_get(v___y_742_, 5);
v_customCanUnfoldPredicate_x3f_754_ = lean_ctor_get(v___y_742_, 6);
v_univApprox_755_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_756_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*7 + 2);
v_cacheInferType_757_ = lean_ctor_get_uint8(v___y_742_, sizeof(void*)*7 + 3);
v_isSharedCheck_907_ = !lean_is_exclusive(v___y_742_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___y_742_, 0);
lean_dec(v_unused_908_);
v___x_759_ = v___y_742_;
v_isShared_760_ = v_isSharedCheck_907_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_754_);
lean_inc(v_synthPendingDepth_753_);
lean_inc(v_defEqCtx_x3f_752_);
lean_inc(v_localInstances_751_);
lean_inc(v_lctx_750_);
lean_inc(v_zetaDeltaSet_749_);
lean_dec(v___y_742_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_907_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_currRecDepth_761_; lean_object* v_ref_762_; uint8_t v_suppressElabErrors_763_; uint8_t v_isRecordingDeps_764_; lean_object* v_fileName_765_; lean_object* v_fileMap_766_; lean_object* v_options_767_; lean_object* v_currNamespace_768_; lean_object* v_openDecls_769_; lean_object* v_initHeartbeats_770_; lean_object* v_maxHeartbeats_771_; lean_object* v_quotContext_772_; lean_object* v_currMacroScope_773_; lean_object* v_cancelTk_x3f_774_; lean_object* v_inheritedTraceOptions_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_905_; 
v_currRecDepth_761_ = lean_ctor_get(v___y_744_, 1);
v_ref_762_ = lean_ctor_get(v___y_744_, 2);
v_suppressElabErrors_763_ = lean_ctor_get_uint8(v___y_744_, sizeof(void*)*3 + 2);
v_isRecordingDeps_764_ = lean_ctor_get_uint8(v___y_744_, sizeof(void*)*3 + 3);
v_fileName_765_ = lean_ctor_get(v_toCold_747_, 0);
v_fileMap_766_ = lean_ctor_get(v_toCold_747_, 1);
v_options_767_ = lean_ctor_get(v_toCold_747_, 2);
v_currNamespace_768_ = lean_ctor_get(v_toCold_747_, 4);
v_openDecls_769_ = lean_ctor_get(v_toCold_747_, 5);
v_initHeartbeats_770_ = lean_ctor_get(v_toCold_747_, 6);
v_maxHeartbeats_771_ = lean_ctor_get(v_toCold_747_, 7);
v_quotContext_772_ = lean_ctor_get(v_toCold_747_, 8);
v_currMacroScope_773_ = lean_ctor_get(v_toCold_747_, 9);
v_cancelTk_x3f_774_ = lean_ctor_get(v_toCold_747_, 10);
v_inheritedTraceOptions_775_ = lean_ctor_get(v_toCold_747_, 11);
v_isSharedCheck_905_ = !lean_is_exclusive(v_toCold_747_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v_toCold_747_, 3);
lean_dec(v_unused_906_);
v___x_777_ = v_toCold_747_;
v_isShared_778_ = v_isSharedCheck_905_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_inheritedTraceOptions_775_);
lean_inc(v_cancelTk_x3f_774_);
lean_inc(v_currMacroScope_773_);
lean_inc(v_quotContext_772_);
lean_inc(v_maxHeartbeats_771_);
lean_inc(v_initHeartbeats_770_);
lean_inc(v_openDecls_769_);
lean_inc(v_currNamespace_768_);
lean_inc(v_options_767_);
lean_inc(v_fileMap_766_);
lean_inc(v_fileName_765_);
lean_dec(v_toCold_747_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_905_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint64_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_779_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_737_);
v___x_780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_780_, 0, v___x_737_);
lean_ctor_set_uint64(v___x_780_, sizeof(void*)*1, v___x_779_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_780_);
v___x_782_ = v___x_759_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_zetaDeltaSet_749_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_lctx_750_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_localInstances_751_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_defEqCtx_x3f_752_);
lean_ctor_set(v_reuseFailAlloc_904_, 5, v_synthPendingDepth_753_);
lean_ctor_set(v_reuseFailAlloc_904_, 6, v_customCanUnfoldPredicate_x3f_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*7, v_trackZetaDelta_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*7 + 1, v_univApprox_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*7 + 2, v_inTypeClassResolution_756_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*7 + 3, v_cacheInferType_757_);
v___x_782_ = v_reuseFailAlloc_904_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___y_784_; uint16_t v___y_785_; lean_object* v_fileName_786_; lean_object* v_fileMap_787_; lean_object* v_currNamespace_788_; lean_object* v_openDecls_789_; lean_object* v_initHeartbeats_790_; lean_object* v_maxHeartbeats_791_; lean_object* v_quotContext_792_; lean_object* v_currMacroScope_793_; lean_object* v_cancelTk_x3f_794_; lean_object* v_inheritedTraceOptions_795_; lean_object* v_currRecDepth_796_; lean_object* v_ref_797_; uint8_t v_suppressElabErrors_798_; uint8_t v_isRecordingDeps_799_; lean_object* v___y_800_; lean_object* v___y_867_; uint16_t v___y_868_; uint8_t v___y_869_; lean_object* v___y_892_; 
if (v_isRecordingDeps_764_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_Meta_smartUnfolding;
v___x_902_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_767_, v___x_901_, v_a_741_);
v___y_892_ = v___x_902_;
goto v___jp_891_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_767_);
v___y_892_ = v___x_903_;
goto v___jp_891_;
}
v___jp_783_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_801_ = l_Lean_maxRecDepth;
v___x_802_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v___y_784_, v___x_801_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 11, v_inheritedTraceOptions_795_);
lean_ctor_set(v___x_777_, 10, v_cancelTk_x3f_794_);
lean_ctor_set(v___x_777_, 9, v_currMacroScope_793_);
lean_ctor_set(v___x_777_, 8, v_quotContext_792_);
lean_ctor_set(v___x_777_, 7, v_maxHeartbeats_791_);
lean_ctor_set(v___x_777_, 6, v_initHeartbeats_790_);
lean_ctor_set(v___x_777_, 5, v_openDecls_789_);
lean_ctor_set(v___x_777_, 4, v_currNamespace_788_);
lean_ctor_set(v___x_777_, 3, v___x_802_);
lean_ctor_set(v___x_777_, 2, v___y_784_);
lean_ctor_set(v___x_777_, 1, v_fileMap_787_);
lean_ctor_set(v___x_777_, 0, v_fileName_786_);
v___x_804_ = v___x_777_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fileName_786_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_fileMap_787_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___y_784_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_currNamespace_788_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v_openDecls_789_);
lean_ctor_set(v_reuseFailAlloc_865_, 6, v_initHeartbeats_790_);
lean_ctor_set(v_reuseFailAlloc_865_, 7, v_maxHeartbeats_791_);
lean_ctor_set(v_reuseFailAlloc_865_, 8, v_quotContext_792_);
lean_ctor_set(v_reuseFailAlloc_865_, 9, v_currMacroScope_793_);
lean_ctor_set(v_reuseFailAlloc_865_, 10, v_cancelTk_x3f_794_);
lean_ctor_set(v_reuseFailAlloc_865_, 11, v_inheritedTraceOptions_795_);
v___x_804_ = v_reuseFailAlloc_865_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_currRecDepth_796_);
lean_ctor_set(v___x_805_, 2, v_ref_797_);
lean_ctor_set_uint16(v___x_805_, sizeof(void*)*3, v___y_785_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*3 + 2, v_suppressElabErrors_798_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*3 + 3, v_isRecordingDeps_799_);
v___x_806_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_lhs_738_, v_rhs_739_, v___x_782_, v___y_743_, v___x_805_, v___y_800_);
lean_dec_ref_known(v___x_805_, 3);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_856_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_856_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_856_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_856_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_fst_811_; lean_object* v_snd_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_855_; 
v_fst_811_ = lean_ctor_get(v_a_807_, 0);
v_snd_812_ = lean_ctor_get(v_a_807_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_a_807_);
if (v_isSharedCheck_855_ == 0)
{
v___x_814_ = v_a_807_;
v_isShared_815_ = v_isSharedCheck_855_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snd_812_);
lean_inc(v_fst_811_);
lean_dec(v_a_807_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_855_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__1, &l_Lean_validateDefEqAttr___lam__0___closed__1_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__1);
lean_inc(v_fst_811_);
v___x_817_ = l_Lean_indentExpr(v_fst_811_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 7);
lean_ctor_set(v___x_814_, 1, v___x_817_);
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_854_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_env_825_; uint8_t v_isExporting_826_; 
v___x_820_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__3, &l_Lean_validateDefEqAttr___lam__0___closed__3_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__3);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
lean_inc(v_snd_812_);
v___x_822_ = l_Lean_indentExpr(v_snd_812_);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_st_ref_get(v___y_745_);
v_env_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref(v_env_825_);
lean_dec(v___x_824_);
v_isExporting_826_ = lean_ctor_get_uint8(v_env_825_, sizeof(void*)*13);
lean_dec_ref(v_env_825_);
if (v_isExporting_826_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_snd_812_);
lean_dec(v_fst_811_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___y_744_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_823_);
v___x_828_ = v___x_809_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_809_);
v___x_830_ = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed), 7, 2);
lean_closure_set(v___x_830_, 0, v_fst_811_);
lean_closure_set(v___x_830_, 1, v_snd_812_);
v___x_831_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___x_830_, v___x_740_, v___x_782_, v___y_743_, v___y_744_, v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___x_782_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_845_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_845_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_845_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___x_836_; 
v___x_836_ = lean_unbox(v_a_832_);
lean_dec(v_a_832_);
if (v___x_836_ == 0)
{
lean_object* v___x_838_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_823_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_823_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_obj_once(&l_Lean_validateDefEqAttr___lam__0___closed__6, &l_Lean_validateDefEqAttr___lam__0___closed__6_once, _init_l_Lean_validateDefEqAttr___lam__0___closed__6);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_823_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_841_);
v___x_843_ = v___x_834_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
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
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref_known(v___x_823_, 2);
v_a_846_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_831_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_831_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
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
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___x_782_);
lean_dec_ref(v___y_744_);
v_a_857_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_806_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_806_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
v___jp_866_:
{
lean_object* v___x_870_; lean_object* v_env_871_; lean_object* v_nextMacroScope_872_; lean_object* v_ngen_873_; lean_object* v_auxDeclNGen_874_; lean_object* v_traceState_875_; lean_object* v_recordedDeps_876_; lean_object* v_messages_877_; lean_object* v_infoState_878_; lean_object* v_snapshotTasks_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_889_; 
v___x_870_ = lean_st_ref_take(v___y_745_);
v_env_871_ = lean_ctor_get(v___x_870_, 0);
v_nextMacroScope_872_ = lean_ctor_get(v___x_870_, 1);
v_ngen_873_ = lean_ctor_get(v___x_870_, 2);
v_auxDeclNGen_874_ = lean_ctor_get(v___x_870_, 3);
v_traceState_875_ = lean_ctor_get(v___x_870_, 4);
v_recordedDeps_876_ = lean_ctor_get(v___x_870_, 6);
v_messages_877_ = lean_ctor_get(v___x_870_, 7);
v_infoState_878_ = lean_ctor_get(v___x_870_, 8);
v_snapshotTasks_879_ = lean_ctor_get(v___x_870_, 9);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_870_, 5);
lean_dec(v_unused_890_);
v___x_881_ = v___x_870_;
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snapshotTasks_879_);
lean_inc(v_infoState_878_);
lean_inc(v_messages_877_);
lean_inc(v_recordedDeps_876_);
lean_inc(v_traceState_875_);
lean_inc(v_auxDeclNGen_874_);
lean_inc(v_ngen_873_);
lean_inc(v_nextMacroScope_872_);
lean_inc(v_env_871_);
lean_dec(v___x_870_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = l_Lean_Kernel_enableDiag(v_env_871_, v___y_869_);
v___x_884_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 5, v___x_884_);
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_nextMacroScope_872_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_ngen_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_auxDeclNGen_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_traceState_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_recordedDeps_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_messages_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_infoState_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 9, v_snapshotTasks_879_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_st_ref_put(v___y_745_, v___x_886_);
lean_inc(v_ref_762_);
lean_inc(v_currRecDepth_761_);
v___y_784_ = v___y_867_;
v___y_785_ = v___y_868_;
v_fileName_786_ = v_fileName_765_;
v_fileMap_787_ = v_fileMap_766_;
v_currNamespace_788_ = v_currNamespace_768_;
v_openDecls_789_ = v_openDecls_769_;
v_initHeartbeats_790_ = v_initHeartbeats_770_;
v_maxHeartbeats_791_ = v_maxHeartbeats_771_;
v_quotContext_792_ = v_quotContext_772_;
v_currMacroScope_793_ = v_currMacroScope_773_;
v_cancelTk_x3f_794_ = v_cancelTk_x3f_774_;
v_inheritedTraceOptions_795_ = v_inheritedTraceOptions_775_;
v_currRecDepth_796_ = v_currRecDepth_761_;
v_ref_797_ = v_ref_762_;
v_suppressElabErrors_798_ = v_suppressElabErrors_763_;
v_isRecordingDeps_799_ = v_isRecordingDeps_764_;
v___y_800_ = v___y_745_;
goto v___jp_783_;
}
}
}
v___jp_891_:
{
uint16_t v___x_893_; lean_object* v___x_894_; lean_object* v_env_895_; uint8_t v___x_896_; uint16_t v___x_897_; uint16_t v___x_898_; uint16_t v___x_899_; uint8_t v___x_900_; 
v___x_893_ = l_Lean_OptionFlags_ofOptions(v___y_892_);
v___x_894_ = lean_st_ref_get(v___y_745_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_894_);
v___x_896_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_895_);
lean_dec_ref(v_env_895_);
v___x_897_ = 512;
v___x_898_ = lean_uint16_land(v___x_893_, v___x_897_);
v___x_899_ = 0;
v___x_900_ = lean_uint16_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
if (v___x_896_ == 0)
{
v___y_867_ = v___y_892_;
v___y_868_ = v___x_893_;
v___y_869_ = v___x_740_;
goto v___jp_866_;
}
else
{
lean_inc(v_ref_762_);
lean_inc(v_currRecDepth_761_);
v___y_784_ = v___y_892_;
v___y_785_ = v___x_893_;
v_fileName_786_ = v_fileName_765_;
v_fileMap_787_ = v_fileMap_766_;
v_currNamespace_788_ = v_currNamespace_768_;
v_openDecls_789_ = v_openDecls_769_;
v_initHeartbeats_790_ = v_initHeartbeats_770_;
v_maxHeartbeats_791_ = v_maxHeartbeats_771_;
v_quotContext_792_ = v_quotContext_772_;
v_currMacroScope_793_ = v_currMacroScope_773_;
v_cancelTk_x3f_794_ = v_cancelTk_x3f_774_;
v_inheritedTraceOptions_795_ = v_inheritedTraceOptions_775_;
v_currRecDepth_796_ = v_currRecDepth_761_;
v_ref_797_ = v_ref_762_;
v_suppressElabErrors_798_ = v_suppressElabErrors_763_;
v_isRecordingDeps_799_ = v_isRecordingDeps_764_;
v___y_800_ = v___y_745_;
goto v___jp_783_;
}
}
else
{
if (v___x_896_ == 0)
{
lean_inc(v_ref_762_);
lean_inc(v_currRecDepth_761_);
v___y_784_ = v___y_892_;
v___y_785_ = v___x_893_;
v_fileName_786_ = v_fileName_765_;
v_fileMap_787_ = v_fileMap_766_;
v_currNamespace_788_ = v_currNamespace_768_;
v_openDecls_789_ = v_openDecls_769_;
v_initHeartbeats_790_ = v_initHeartbeats_770_;
v_maxHeartbeats_791_ = v_maxHeartbeats_771_;
v_quotContext_792_ = v_quotContext_772_;
v_currMacroScope_793_ = v_currMacroScope_773_;
v_cancelTk_x3f_794_ = v_cancelTk_x3f_774_;
v_inheritedTraceOptions_795_ = v_inheritedTraceOptions_775_;
v_currRecDepth_796_ = v_currRecDepth_761_;
v_ref_797_ = v_ref_762_;
v_suppressElabErrors_798_ = v_suppressElabErrors_763_;
v_isRecordingDeps_799_ = v_isRecordingDeps_764_;
v___y_800_ = v___y_745_;
goto v___jp_783_;
}
else
{
v___y_867_ = v___y_892_;
v___y_868_ = v___x_893_;
v___y_869_ = v_a_741_;
goto v___jp_866_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_validateDefEqAttr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_737_ = stack[0].m_obj;
lean_object* v_lhs_738_ = stack[1].m_obj;
lean_object* v_rhs_739_ = stack[2].m_obj;
uint8_t v___x_740_ = stack[3].m_num;
uint8_t v_a_741_ = stack[4].m_num;
lean_object* v___y_742_ = stack[5].m_obj;
lean_object* v___y_743_ = stack[6].m_obj;
lean_object* v___y_744_ = stack[7].m_obj;
lean_object* v___y_745_ = stack[8].m_obj;
lean_object* v_res_909_;
v_res_909_ = l_Lean_validateDefEqAttr___lam__0(v___x_737_, v_lhs_738_, v_rhs_739_, v___x_740_, v_a_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0___boxed(lean_object* v___x_910_, lean_object* v_lhs_911_, lean_object* v_rhs_912_, lean_object* v___x_913_, lean_object* v_a_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_8983__boxed_920_; uint8_t v_a_8984__boxed_921_; lean_object* v_res_922_; 
v___x_8983__boxed_920_ = lean_unbox(v___x_913_);
v_a_8984__boxed_921_ = lean_unbox(v_a_914_);
v_res_922_ = l_Lean_validateDefEqAttr___lam__0(v___x_910_, v_lhs_911_, v_rhs_912_, v___x_8983__boxed_920_, v_a_8984__boxed_921_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec(v___y_916_);
return v_res_922_;
}
}
lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* v_lhs_923_, lean_object* v_rhs_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
lean_inc_ref(v_rhs_924_);
lean_inc_ref(v_lhs_923_);
v___x_930_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(v_lhs_923_, v_rhs_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_950_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_950_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; 
v___x_935_ = lean_unbox(v_a_931_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_933_);
v___x_936_ = 1;
v___x_937_ = l_Lean_Meta_Context_config(v___y_925_);
v___x_938_ = lean_box(v___x_936_);
lean_inc_ref(v_rhs_924_);
lean_inc_ref(v_lhs_923_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0___boxed), 10, 5);
lean_closure_set(v___f_939_, 0, v___x_937_);
lean_closure_set(v___f_939_, 1, v_lhs_923_);
lean_closure_set(v___f_939_, 2, v_rhs_924_);
lean_closure_set(v___f_939_, 3, v___x_938_);
lean_closure_set(v___f_939_, 4, v_a_931_);
v___x_940_ = lean_unsigned_to_nat(2u);
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_940_);
v___x_942_ = lean_array_push(v___x_941_, v_lhs_923_);
v___x_943_ = lean_array_push(v___x_942_, v_rhs_924_);
v___x_944_ = l_Lean_MessageData_ofLazyM(v___f_939_, v___x_943_);
v___x_945_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_944_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_a_931_);
lean_dec_ref(v_rhs_924_);
lean_dec_ref(v_lhs_923_);
v___x_946_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_946_);
v___x_948_ = v___x_933_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v_rhs_924_);
lean_dec_ref(v_lhs_923_);
v_a_951_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_930_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_930_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_validateDefEqAttr___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_923_ = stack[0].m_obj;
lean_object* v_rhs_924_ = stack[1].m_obj;
lean_object* v___y_925_ = stack[2].m_obj;
lean_object* v___y_926_ = stack[3].m_obj;
lean_object* v___y_927_ = stack[4].m_obj;
lean_object* v___y_928_ = stack[5].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_923_, v_rhs_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* v_lhs_960_, lean_object* v_rhs_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_validateDefEqAttr___lam__1(v_lhs_960_, v_rhs_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_971_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
lean_ctor_set(v___x_973_, 3, v___x_972_);
lean_ctor_set(v___x_973_, 4, v___x_971_);
lean_ctor_set(v___x_973_, 5, v___x_971_);
lean_ctor_set(v___x_973_, 6, v___x_971_);
lean_ctor_set(v___x_973_, 7, v___x_971_);
lean_ctor_set(v___x_973_, 8, v___x_971_);
lean_ctor_set(v___x_973_, 9, v___x_971_);
lean_ctor_set(v___x_973_, 10, v___x_971_);
lean_ctor_set(v___x_973_, 11, v___x_970_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(32u);
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_977_ = ((size_t)5ULL);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_unsigned_to_nat(32u);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
v___x_981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_982_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
lean_ctor_set(v___x_982_, 2, v___x_978_);
lean_ctor_set(v___x_982_, 3, v___x_978_);
lean_ctor_set_usize(v___x_982_, 4, v___x_977_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_box(1);
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
lean_ctor_set(v___x_986_, 2, v___x_983_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__21));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__23));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__25));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1020_, lean_object* v_declHint_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_env_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_st_ref_get(v___y_1022_);
v_env_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_ref(v_env_1026_);
lean_dec(v___x_1025_);
v___x_1027_ = l_Lean_Name_isAnonymous(v_declHint_1021_);
if (v___x_1027_ == 0)
{
uint8_t v_isExporting_1028_; 
v_isExporting_1028_ = lean_ctor_get_uint8(v_env_1026_, sizeof(void*)*13);
if (v_isExporting_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v_env_1026_);
lean_dec(v_declHint_1021_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_msg_1020_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
lean_inc_ref(v_env_1026_);
v___x_1030_ = l_Lean_Environment_setExporting(v_env_1026_, v___x_1027_);
lean_inc(v_declHint_1021_);
lean_inc_ref(v___x_1030_);
v___x_1031_ = l_Lean_Environment_contains(v___x_1030_, v_declHint_1021_, v_isExporting_1028_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_env_1026_);
lean_dec(v_declHint_1021_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_msg_1020_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_c_1038_; lean_object* v___x_1039_; 
v___x_1033_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1035_ = l_Lean_Options_empty;
v___x_1036_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1030_);
lean_ctor_set(v___x_1036_, 1, v___x_1033_);
lean_ctor_set(v___x_1036_, 2, v___x_1034_);
lean_ctor_set(v___x_1036_, 3, v___x_1035_);
lean_inc(v_declHint_1021_);
v___x_1037_ = l_Lean_MessageData_ofConstName(v_declHint_1021_, v___x_1027_);
v_c_1038_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1038_, 0, v___x_1036_);
lean_ctor_set(v_c_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1026_, v_declHint_1021_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v_env_1026_);
lean_dec(v_declHint_1021_);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_c_1038_);
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_MessageData_note(v___x_1043_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_msg_1020_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v_val_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1103_; 
v_val_1047_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1049_ = v___x_1039_;
v_isShared_1050_ = v_isSharedCheck_1103_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_val_1047_);
lean_dec(v___x_1039_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1103_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v_modules_1052_; lean_object* v_moduleNames_1053_; lean_object* v_mod_1054_; uint8_t v___y_1056_; uint8_t v___x_1086_; 
v___x_1051_ = l_Lean_Environment_header(v_env_1026_);
lean_dec_ref(v_env_1026_);
v_modules_1052_ = lean_ctor_get(v___x_1051_, 3);
lean_inc_ref(v_modules_1052_);
v_moduleNames_1053_ = lean_ctor_get(v___x_1051_, 4);
lean_inc_ref(v_moduleNames_1053_);
lean_dec_ref(v___x_1051_);
v_mod_1054_ = lean_array_get(v___x_1024_, v_moduleNames_1053_, v_val_1047_);
lean_dec_ref(v_moduleNames_1053_);
v___x_1086_ = l_Lean_isPrivateName(v_declHint_1021_);
lean_dec(v_declHint_1021_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_array_get_size(v_modules_1052_);
v___x_1088_ = lean_nat_dec_lt(v_val_1047_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v_modules_1052_);
lean_dec(v_val_1047_);
v___y_1056_ = v___x_1086_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1089_; lean_object* v_toImport_1090_; uint8_t v_isExported_1091_; 
v___x_1089_ = lean_array_fget(v_modules_1052_, v_val_1047_);
lean_dec(v_val_1047_);
lean_dec_ref(v_modules_1052_);
v_toImport_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_toImport_1090_);
lean_dec(v___x_1089_);
v_isExported_1091_ = lean_ctor_get_uint8(v_toImport_1090_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1090_);
v___y_1056_ = v_isExported_1091_;
goto v___jp_1055_;
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref(v_modules_1052_);
lean_del_object(v___x_1049_);
lean_dec(v_val_1047_);
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_c_1038_);
v___x_1094_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_MessageData_ofName(v_mod_1054_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_MessageData_note(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_msg_1020_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1055_:
{
if (v___y_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_c_1038_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_ofName(v_mod_1054_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_note(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1020_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1066_);
v___x_1068_ = v___x_1049_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_c_1038_);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_MessageData_ofName(v_mod_1054_);
lean_inc_ref(v___x_1074_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1074_);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_note(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_msg_1020_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1082_);
v___x_1084_ = v___x_1049_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
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
lean_object* v___x_1104_; 
lean_dec_ref(v_env_1026_);
lean_dec(v_declHint_1021_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_msg_1020_);
return v___x_1104_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1020_ = stack[0].m_obj;
lean_object* v_declHint_1021_ = stack[1].m_obj;
lean_object* v___y_1022_ = stack[2].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1020_, v_declHint_1021_, v___y_1022_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1106_, v_declHint_1107_, v___y_1108_);
lean_dec(v___y_1108_);
return v_res_1110_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1111_, lean_object* v_declHint_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1126_; 
v___x_1116_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1111_, v_declHint_1112_, v___y_1114_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = l_Lean_unknownIdentifierMessageTag;
v___x_1122_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_a_1117_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1111_ = stack[0].m_obj;
lean_object* v_declHint_1112_ = stack[1].m_obj;
lean_object* v___y_1113_ = stack[2].m_obj;
lean_object* v___y_1114_ = stack[3].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1111_, v_declHint_1112_, v___y_1113_, v___y_1114_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1128_, lean_object* v_declHint_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1128_, v_declHint_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1133_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v_toCold_1139_; lean_object* v_env_1140_; lean_object* v_options_1141_; uint8_t v___x_1142_; lean_object* v_env_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1138_ = lean_st_ref_get(v___y_1136_);
v_toCold_1139_ = lean_ctor_get(v___y_1135_, 0);
v_env_1140_ = lean_ctor_get(v___x_1138_, 0);
lean_inc_ref(v_env_1140_);
lean_dec(v___x_1138_);
v_options_1141_ = lean_ctor_get(v_toCold_1139_, 2);
v___x_1142_ = 0;
v_env_1143_ = l_Lean_Environment_setRecordingDeps(v_env_1140_, v___x_1142_);
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1145_ = lean_unsigned_to_nat(32u);
v___x_1146_ = lean_mk_empty_array_with_capacity(v___x_1145_);
lean_dec_ref(v___x_1146_);
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
lean_inc_ref(v_options_1141_);
v___x_1148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1148_, 0, v_env_1143_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
lean_ctor_set(v___x_1148_, 2, v___x_1147_);
lean_ctor_set(v___x_1148_, 3, v_options_1141_);
v___x_1149_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v_msgData_1134_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1134_ = stack[0].m_obj;
lean_object* v___y_1135_ = stack[1].m_obj;
lean_object* v___y_1136_ = stack[2].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_1134_, v___y_1135_, v___y_1136_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1156_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_ref_1161_; lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_ref_1161_ = lean_ctor_get(v___y_1158_, 2);
v___x_1162_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_1157_, v___y_1158_, v___y_1159_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_inc(v_ref_1161_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_ref_1161_);
lean_ctor_set(v___x_1167_, 1, v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 1);
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1157_ = stack[0].m_obj;
lean_object* v___y_1158_ = stack[1].m_obj;
lean_object* v___y_1159_ = stack[2].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1157_, v___y_1158_, v___y_1159_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1177_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1178_, lean_object* v_msg_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_toCold_1183_; lean_object* v_currRecDepth_1184_; lean_object* v_ref_1185_; uint16_t v_optionFlags_1186_; uint8_t v_suppressElabErrors_1187_; uint8_t v_isRecordingDeps_1188_; lean_object* v_ref_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_toCold_1183_ = lean_ctor_get(v___y_1180_, 0);
v_currRecDepth_1184_ = lean_ctor_get(v___y_1180_, 1);
v_ref_1185_ = lean_ctor_get(v___y_1180_, 2);
v_optionFlags_1186_ = lean_ctor_get_uint16(v___y_1180_, sizeof(void*)*3);
v_suppressElabErrors_1187_ = lean_ctor_get_uint8(v___y_1180_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1188_ = lean_ctor_get_uint8(v___y_1180_, sizeof(void*)*3 + 3);
v_ref_1189_ = l_Lean_replaceRef(v_ref_1178_, v_ref_1185_);
lean_inc(v_currRecDepth_1184_);
lean_inc_ref(v_toCold_1183_);
v___x_1190_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1190_, 0, v_toCold_1183_);
lean_ctor_set(v___x_1190_, 1, v_currRecDepth_1184_);
lean_ctor_set(v___x_1190_, 2, v_ref_1189_);
lean_ctor_set_uint16(v___x_1190_, sizeof(void*)*3, v_optionFlags_1186_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*3 + 2, v_suppressElabErrors_1187_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*3 + 3, v_isRecordingDeps_1188_);
v___x_1191_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1179_, v___x_1190_, v___y_1181_);
lean_dec_ref_known(v___x_1190_, 3);
return v___x_1191_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1178_ = stack[0].m_obj;
lean_object* v_msg_1179_ = stack[1].m_obj;
lean_object* v___y_1180_ = stack[2].m_obj;
lean_object* v___y_1181_ = stack[3].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1178_, v_msg_1179_, v___y_1180_, v___y_1181_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1193_, lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1193_, v_msg_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v_ref_1193_);
return v_res_1198_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v_declHint_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1200_, v_declHint_1201_, v___y_1202_, v___y_1203_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1199_, v_a_1206_, v___y_1202_, v___y_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1199_ = stack[0].m_obj;
lean_object* v_msg_1200_ = stack[1].m_obj;
lean_object* v_declHint_1201_ = stack[2].m_obj;
lean_object* v___y_1202_ = stack[3].m_obj;
lean_object* v___y_1203_ = stack[4].m_obj;
lean_object* v_res_1208_;
v_res_1208_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1199_, v_msg_1200_, v_declHint_1201_, v___y_1202_, v___y_1203_);
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1209_, lean_object* v_msg_1210_, lean_object* v_declHint_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1209_, v_msg_1210_, v_declHint_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v_ref_1209_);
return v_res_1215_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1222_, lean_object* v_constName_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1227_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1228_ = 0;
lean_inc(v_constName_1223_);
v___x_1229_ = l_Lean_MessageData_ofConstName(v_constName_1223_, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1227_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1222_, v___x_1232_, v_constName_1223_, v___y_1224_, v___y_1225_);
return v___x_1233_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1222_ = stack[0].m_obj;
lean_object* v_constName_1223_ = stack[1].m_obj;
lean_object* v___y_1224_ = stack[2].m_obj;
lean_object* v___y_1225_ = stack[3].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1222_, v_constName_1223_, v___y_1224_, v___y_1225_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_constName_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1235_, v_constName_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v_ref_1235_);
return v_res_1240_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(lean_object* v_constName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_ref_1245_; lean_object* v___x_1246_; 
v_ref_1245_ = lean_ctor_get(v___y_1242_, 2);
v___x_1246_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1245_, v_constName_1241_, v___y_1242_, v___y_1243_);
return v___x_1246_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1241_ = stack[0].m_obj;
lean_object* v___y_1242_ = stack[1].m_obj;
lean_object* v___y_1243_ = stack[2].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1241_, v___y_1242_, v___y_1243_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1252_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_env_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_st_ref_get(v___y_1255_);
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_env_1258_);
lean_dec(v___x_1257_);
v___x_1259_ = 0;
lean_inc(v_constName_1253_);
v___x_1260_ = l_Lean_Environment_findConstVal_x3f(v_env_1258_, v_constName_1253_, v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1253_, v___y_1254_, v___y_1255_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_constName_1253_);
v_val_1262_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1260_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v___x_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 0);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_val_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1253_ = stack[0].m_obj;
lean_object* v___y_1254_ = stack[1].m_obj;
lean_object* v___y_1255_ = stack[2].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1253_, v___y_1254_, v___y_1255_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_constName_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1275_;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__2(void){
_start:
{
lean_object* v___x_1283_; uint64_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__1));
v___x_1284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3(void){
_start:
{
uint64_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_uint64_once(&l_Lean_validateDefEqAttr___closed__2, &l_Lean_validateDefEqAttr___closed__2_once, _init_l_Lean_validateDefEqAttr___closed__2);
v___x_1286_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__1));
v___x_1287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set_uint64(v___x_1287_, sizeof(void*)*1, v___x_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_box(1);
v___x_1291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1292_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1290_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7(void){
_start:
{
uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1296_ = 1;
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_box(0);
v___x_1299_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__6));
v___x_1300_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__5, &l_Lean_validateDefEqAttr___closed__5_once, _init_l_Lean_validateDefEqAttr___closed__5);
v___x_1301_ = lean_box(1);
v___x_1302_ = 0;
v___x_1303_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__3, &l_Lean_validateDefEqAttr___closed__3_once, _init_l_Lean_validateDefEqAttr___closed__3);
v___x_1304_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1301_);
lean_ctor_set(v___x_1304_, 2, v___x_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1299_);
lean_ctor_set(v___x_1304_, 4, v___x_1298_);
lean_ctor_set(v___x_1304_, 5, v___x_1297_);
lean_ctor_set(v___x_1304_, 6, v___x_1298_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7, v___x_1302_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 1, v___x_1302_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 2, v___x_1302_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*7 + 3, v___x_1296_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1306_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_ctor_set(v___x_1308_, 2, v___x_1307_);
lean_ctor_set(v___x_1308_, 3, v___x_1307_);
lean_ctor_set(v___x_1308_, 4, v___x_1306_);
lean_ctor_set(v___x_1308_, 5, v___x_1306_);
lean_ctor_set(v___x_1308_, 6, v___x_1306_);
lean_ctor_set(v___x_1308_, 7, v___x_1306_);
lean_ctor_set(v___x_1308_, 8, v___x_1306_);
lean_ctor_set(v___x_1308_, 9, v___x_1306_);
lean_ctor_set(v___x_1308_, 10, v___x_1306_);
lean_ctor_set(v___x_1308_, 11, v___x_1305_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
lean_ctor_set(v___x_1310_, 3, v___x_1309_);
lean_ctor_set(v___x_1310_, 4, v___x_1309_);
lean_ctor_set(v___x_1310_, 5, v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__4, &l_Lean_validateDefEqAttr___closed__4_once, _init_l_Lean_validateDefEqAttr___closed__4);
v___x_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
lean_ctor_set(v___x_1312_, 3, v___x_1311_);
lean_ctor_set(v___x_1312_, 4, v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1313_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__10, &l_Lean_validateDefEqAttr___closed__10_once, _init_l_Lean_validateDefEqAttr___closed__10);
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1315_ = lean_box(1);
v___x_1316_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__9, &l_Lean_validateDefEqAttr___closed__9_once, _init_l_Lean_validateDefEqAttr___closed__9);
v___x_1317_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__8, &l_Lean_validateDefEqAttr___closed__8_once, _init_l_Lean_validateDefEqAttr___closed__8);
v___x_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
lean_ctor_set(v___x_1318_, 2, v___x_1315_);
lean_ctor_set(v___x_1318_, 3, v___x_1314_);
lean_ctor_set(v___x_1318_, 4, v___x_1313_);
return v___x_1318_;
}
}
lean_object* l_Lean_validateDefEqAttr(lean_object* v_declName_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v___f_1323_; lean_object* v___x_1324_; 
v___f_1323_ = ((lean_object*)(l_Lean_validateDefEqAttr___closed__0));
v___x_1324_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(v_declName_1319_, v_a_1320_, v_a_1321_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_type_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v_type_1326_ = lean_ctor_get(v_a_1325_, 2);
lean_inc_ref(v_type_1326_);
lean_dec(v_a_1325_);
v___x_1327_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__7, &l_Lean_validateDefEqAttr___closed__7_once, _init_l_Lean_validateDefEqAttr___closed__7);
v___x_1328_ = lean_obj_once(&l_Lean_validateDefEqAttr___closed__11, &l_Lean_validateDefEqAttr___closed__11_once, _init_l_Lean_validateDefEqAttr___closed__11);
v___x_1329_ = lean_st_mk_ref(v___x_1328_);
v___x_1330_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v_type_1326_, v___f_1323_, v___x_1327_, v___x_1329_, v_a_1320_, v_a_1321_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_st_ref_get(v___x_1329_);
lean_dec(v___x_1329_);
lean_dec(v___x_1335_);
if (v_isShared_1334_ == 0)
{
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1331_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_dec(v___x_1329_);
return v___x_1330_;
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1324_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1324_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_validateDefEqAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1319_ = stack[0].m_obj;
lean_object* v_a_1320_ = stack[1].m_obj;
lean_object* v_a_1321_ = stack[2].m_obj;
lean_object* v_res_1348_;
v_res_1348_ = l_Lean_validateDefEqAttr(v_declName_1319_, v_a_1320_, v_a_1321_);
stack->m_obj
 = v_res_1348_;
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___boxed(lean_object* v_declName_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_validateDefEqAttr(v_declName_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1353_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_1354_, lean_object* v_x_1355_, uint8_t v_isExporting_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_1355_, v_isExporting_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1355_ = stack[1].m_obj;
uint8_t v_isExporting_1356_ = stack[2].m_num;
lean_object* v___y_1357_ = stack[3].m_obj;
lean_object* v___y_1358_ = stack[4].m_obj;
lean_object* v___y_1359_ = stack[5].m_obj;
lean_object* v___y_1360_ = stack[6].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(lean_box(0), v_x_1355_, v_isExporting_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_x_1365_, lean_object* v_isExporting_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_isExporting_boxed_1372_; lean_object* v_res_1373_; 
v_isExporting_boxed_1372_ = lean_unbox(v_isExporting_1366_);
v_res_1373_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_1364_, v_x_1365_, v_isExporting_boxed_1372_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1373_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_object* v_00_u03b1_1374_, lean_object* v_x_1375_, uint8_t v_when_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v_x_1375_, v_when_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1375_ = stack[1].m_obj;
uint8_t v_when_1376_ = stack[2].m_num;
lean_object* v___y_1377_ = stack[3].m_obj;
lean_object* v___y_1378_ = stack[4].m_obj;
lean_object* v___y_1379_ = stack[5].m_obj;
lean_object* v___y_1380_ = stack[6].m_obj;
lean_object* v_res_1383_;
v_res_1383_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(lean_box(0), v_x_1375_, v_when_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
stack->m_obj
 = v_res_1383_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_x_1385_, lean_object* v_when_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_when_boxed_1392_; lean_object* v_res_1393_; 
v_when_boxed_1392_ = lean_unbox(v_when_1386_);
v_res_1393_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(v_00_u03b1_1384_, v_x_1385_, v_when_boxed_1392_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1393_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_object* v_00_u03b1_1394_, lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1395_ = stack[1].m_obj;
lean_object* v___y_1396_ = stack[2].m_obj;
lean_object* v___y_1397_ = stack[3].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(lean_box(0), v_constName_1395_, v___y_1396_, v___y_1397_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_constName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_1401_, v_constName_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1406_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1407_, lean_object* v_ref_1408_, lean_object* v_constName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_1408_, v_constName_1409_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1408_ = stack[1].m_obj;
lean_object* v_constName_1409_ = stack[2].m_obj;
lean_object* v___y_1410_ = stack[3].m_obj;
lean_object* v___y_1411_ = stack[4].m_obj;
lean_object* v_res_1414_;
v_res_1414_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(lean_box(0), v_ref_1408_, v_constName_1409_, v___y_1410_, v___y_1411_);
stack->m_obj
 = v_res_1414_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_ref_1416_, lean_object* v_constName_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_1415_, v_ref_1416_, v_constName_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v_ref_1416_);
return v_res_1421_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1422_, lean_object* v_ref_1423_, lean_object* v_msg_1424_, lean_object* v_declHint_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1423_, v_msg_1424_, v_declHint_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1423_ = stack[1].m_obj;
lean_object* v_msg_1424_ = stack[2].m_obj;
lean_object* v_declHint_1425_ = stack[3].m_obj;
lean_object* v___y_1426_ = stack[4].m_obj;
lean_object* v___y_1427_ = stack[5].m_obj;
lean_object* v_res_1430_;
v_res_1430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(lean_box(0), v_ref_1423_, v_msg_1424_, v_declHint_1425_, v___y_1426_, v___y_1427_);
stack->m_obj
 = v_res_1430_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_ref_1432_, lean_object* v_msg_1433_, lean_object* v_declHint_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1431_, v_ref_1432_, v_msg_1433_, v_declHint_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v_ref_1432_);
return v_res_1438_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1439_, lean_object* v_declHint_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1439_, v_declHint_1440_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1439_ = stack[0].m_obj;
lean_object* v_declHint_1440_ = stack[1].m_obj;
lean_object* v___y_1441_ = stack[2].m_obj;
lean_object* v___y_1442_ = stack[3].m_obj;
lean_object* v_res_1445_;
v_res_1445_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1439_, v_declHint_1440_, v___y_1441_, v___y_1442_);
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1446_, lean_object* v_declHint_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1446_, v_declHint_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1451_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1452_, lean_object* v_ref_1453_, lean_object* v_msg_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1453_, v_msg_1454_, v___y_1455_, v___y_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1453_ = stack[1].m_obj;
lean_object* v_msg_1454_ = stack[2].m_obj;
lean_object* v___y_1455_ = stack[3].m_obj;
lean_object* v___y_1456_ = stack[4].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(lean_box(0), v_ref_1453_, v_msg_1454_, v___y_1455_, v___y_1456_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1460_, v_ref_1461_, v_msg_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v_ref_1461_);
return v_res_1466_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_1468_, v___y_1469_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1468_ = stack[1].m_obj;
lean_object* v___y_1469_ = stack[2].m_obj;
lean_object* v___y_1470_ = stack[3].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(lean_box(0), v_msg_1468_, v___y_1469_, v___y_1470_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_msg_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_1474_, v_msg_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1479_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1493_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1494_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1495_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1496_ = 0;
v___x_1497_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1498_ = 0;
v___x_1499_ = l_Lean_registerTagAttribute(v___x_1492_, v___x_1493_, v___x_1494_, v___x_1495_, v___x_1496_, v___x_1497_, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1500_;
v_res_1500_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
return v_res_1502_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1(){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1506_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0));
v___x_1507_ = l_Lean_addBuiltinDocString(v___x_1505_, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1508_;
v_res_1508_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
return v_res_1510_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1538_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6));
v___x_1539_ = l_Lean_addBuiltinDeclarationRanges(v___x_1537_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1540_;
v_res_1540_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_addEntryFn_1543_, lean_object* v_decl_1544_, lean_object* v_s_1545_){
_start:
{
lean_object* v_importedEntries_1546_; lean_object* v_state_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_importedEntries_1546_ = lean_ctor_get(v_s_1545_, 0);
v_state_1547_ = lean_ctor_get(v_s_1545_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_s_1545_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v_s_1545_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_state_1547_);
lean_inc(v_importedEntries_1546_);
lean_dec(v_s_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_state_1551_; lean_object* v___x_1553_; 
v_state_1551_ = lean_apply_2(v_addEntryFn_1543_, v_state_1547_, v_decl_1544_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v_state_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_importedEntries_1546_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_state_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_attrName_1568_, lean_object* v_declName_1569_, lean_object* v_asyncPrefix_x3f_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___y_1575_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1570_) == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_MessageData_nil;
v___y_1575_ = v___x_1588_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_val_1589_ = lean_ctor_get(v_asyncPrefix_x3f_1570_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_asyncPrefix_x3f_1570_, 1);
v___x_1590_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1591_ = l_Lean_MessageData_ofName(v_val_1589_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___y_1575_ = v___x_1594_;
goto v___jp_1574_;
}
v___jp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1576_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1577_ = l_Lean_MessageData_ofName(v_attrName_1568_);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = 0;
v___x_1582_ = l_Lean_MessageData_ofConstName(v_declName_1569_, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1580_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___y_1575_);
v___x_1587_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1586_, v___y_1571_, v___y_1572_);
return v___x_1587_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1568_ = stack[0].m_obj;
lean_object* v_declName_1569_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_1570_ = stack[2].m_obj;
lean_object* v___y_1571_ = stack[3].m_obj;
lean_object* v___y_1572_ = stack[4].m_obj;
lean_object* v_res_1595_;
v_res_1595_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1568_, v_declName_1569_, v_asyncPrefix_x3f_1570_, v___y_1571_, v___y_1572_);
stack->m_obj
 = v_res_1595_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1596_, lean_object* v_declName_1597_, lean_object* v_asyncPrefix_x3f_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1596_, v_declName_1597_, v_asyncPrefix_x3f_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_attrName_1606_, lean_object* v_declName_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1611_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1612_ = l_Lean_MessageData_ofName(v_attrName_1606_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = 0;
v___x_1617_ = l_Lean_MessageData_ofConstName(v_declName_1607_, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1615_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_1620_, v___y_1608_, v___y_1609_);
return v___x_1621_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1606_ = stack[0].m_obj;
lean_object* v_declName_1607_ = stack[1].m_obj;
lean_object* v___y_1608_ = stack[2].m_obj;
lean_object* v___y_1609_ = stack[3].m_obj;
lean_object* v_res_1622_;
v_res_1622_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1606_, v_declName_1607_, v___y_1608_, v___y_1609_);
stack->m_obj
 = v_res_1622_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1623_, lean_object* v_declName_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1623_, v_declName_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1628_;
}
}
lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(lean_object* v_attr_1629_, lean_object* v_decl_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1651_; lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___x_1687_; 
v___x_1673_ = lean_st_ref_get(v___y_1632_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_ref(v_env_1674_);
lean_dec(v___x_1673_);
v___x_1687_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1674_, v_decl_1630_);
if (lean_obj_tag(v___x_1687_) == 0)
{
v___y_1676_ = v___y_1631_;
v___y_1677_ = v___y_1632_;
goto v___jp_1675_;
}
else
{
lean_object* v_attr_1688_; lean_object* v_toAttributeImplCore_1689_; lean_object* v_name_1690_; lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1687_, 1);
lean_dec_ref(v_env_1674_);
v_attr_1688_ = lean_ctor_get(v_attr_1629_, 0);
lean_inc_ref(v_attr_1688_);
lean_dec_ref(v_attr_1629_);
v_toAttributeImplCore_1689_ = lean_ctor_get(v_attr_1688_, 0);
lean_inc_ref(v_toAttributeImplCore_1689_);
lean_dec_ref(v_attr_1688_);
v_name_1690_ = lean_ctor_get(v_toAttributeImplCore_1689_, 1);
lean_inc(v_name_1690_);
lean_dec_ref(v_toAttributeImplCore_1689_);
v___x_1691_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_1690_, v_decl_1630_, v___y_1631_, v___y_1632_);
return v___x_1691_;
}
v___jp_1634_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
v___x_1647_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1647_, 0, v___y_1645_);
lean_ctor_set(v___x_1647_, 1, v___y_1644_);
lean_ctor_set(v___x_1647_, 2, v___y_1642_);
lean_ctor_set(v___x_1647_, 3, v___y_1637_);
lean_ctor_set(v___x_1647_, 4, v___y_1639_);
lean_ctor_set(v___x_1647_, 5, v___x_1646_);
lean_ctor_set(v___x_1647_, 6, v___y_1636_);
lean_ctor_set(v___x_1647_, 7, v___y_1641_);
lean_ctor_set(v___x_1647_, 8, v___y_1643_);
lean_ctor_set(v___x_1647_, 9, v___y_1635_);
v___x_1648_ = lean_st_ref_put(v___y_1640_, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___y_1638_);
return v___x_1649_;
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v_ext_1653_; lean_object* v_toEnvExtension_1654_; lean_object* v_env_1655_; lean_object* v_nextMacroScope_1656_; lean_object* v_ngen_1657_; lean_object* v_auxDeclNGen_1658_; lean_object* v_traceState_1659_; lean_object* v_recordedDeps_1660_; lean_object* v_messages_1661_; lean_object* v_infoState_1662_; lean_object* v_snapshotTasks_1663_; lean_object* v_addEntryFn_1664_; lean_object* v_asyncMode_1665_; uint8_t v_logWrites_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; uint8_t v___x_1669_; 
v___x_1652_ = lean_st_ref_take(v___y_1651_);
v_ext_1653_ = lean_ctor_get(v_attr_1629_, 1);
lean_inc_ref(v_ext_1653_);
lean_dec_ref(v_attr_1629_);
v_toEnvExtension_1654_ = lean_ctor_get(v_ext_1653_, 0);
lean_inc_ref(v_toEnvExtension_1654_);
v_env_1655_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1655_);
v_nextMacroScope_1656_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_nextMacroScope_1656_);
v_ngen_1657_ = lean_ctor_get(v___x_1652_, 2);
lean_inc_ref(v_ngen_1657_);
v_auxDeclNGen_1658_ = lean_ctor_get(v___x_1652_, 3);
lean_inc_ref(v_auxDeclNGen_1658_);
v_traceState_1659_ = lean_ctor_get(v___x_1652_, 4);
lean_inc_ref(v_traceState_1659_);
v_recordedDeps_1660_ = lean_ctor_get(v___x_1652_, 6);
lean_inc_ref(v_recordedDeps_1660_);
v_messages_1661_ = lean_ctor_get(v___x_1652_, 7);
lean_inc_ref(v_messages_1661_);
v_infoState_1662_ = lean_ctor_get(v___x_1652_, 8);
lean_inc_ref(v_infoState_1662_);
v_snapshotTasks_1663_ = lean_ctor_get(v___x_1652_, 9);
lean_inc_ref(v_snapshotTasks_1663_);
lean_dec(v___x_1652_);
v_addEntryFn_1664_ = lean_ctor_get(v_ext_1653_, 3);
lean_inc(v_addEntryFn_1664_);
lean_dec_ref(v_ext_1653_);
v_asyncMode_1665_ = lean_ctor_get(v_toEnvExtension_1654_, 2);
lean_inc(v_asyncMode_1665_);
v_logWrites_1666_ = lean_ctor_get_uint8(v_toEnvExtension_1654_, sizeof(void*)*6);
v___x_1667_ = lean_box(0);
lean_inc(v_decl_1630_);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___lam__0), 3, 2);
lean_closure_set(v___f_1668_, 0, v_addEntryFn_1664_);
lean_closure_set(v___f_1668_, 1, v_decl_1630_);
v___x_1669_ = 1;
if (v_logWrites_1666_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1654_, v_env_1655_, v___f_1668_, v_asyncMode_1665_, v_decl_1630_, v___x_1669_);
lean_dec(v_asyncMode_1665_);
v___y_1635_ = v_snapshotTasks_1663_;
v___y_1636_ = v_recordedDeps_1660_;
v___y_1637_ = v_auxDeclNGen_1658_;
v___y_1638_ = v___x_1667_;
v___y_1639_ = v_traceState_1659_;
v___y_1640_ = v___y_1651_;
v___y_1641_ = v_messages_1661_;
v___y_1642_ = v_ngen_1657_;
v___y_1643_ = v_infoState_1662_;
v___y_1644_ = v_nextMacroScope_1656_;
v___y_1645_ = v___x_1670_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref(v_toEnvExtension_1654_);
v___x_1671_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1654_, v_env_1655_);
lean_dec_ref(v_env_1655_);
v___x_1672_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1654_, v___x_1671_, v___f_1668_, v_asyncMode_1665_, v_decl_1630_, v___x_1669_);
lean_dec(v_asyncMode_1665_);
v___y_1635_ = v_snapshotTasks_1663_;
v___y_1636_ = v_recordedDeps_1660_;
v___y_1637_ = v_auxDeclNGen_1658_;
v___y_1638_ = v___x_1667_;
v___y_1639_ = v_traceState_1659_;
v___y_1640_ = v___y_1651_;
v___y_1641_ = v_messages_1661_;
v___y_1642_ = v_ngen_1657_;
v___y_1643_ = v_infoState_1662_;
v___y_1644_ = v_nextMacroScope_1656_;
v___y_1645_ = v___x_1672_;
goto v___jp_1634_;
}
}
v___jp_1675_:
{
lean_object* v_ext_1678_; lean_object* v_toEnvExtension_1679_; lean_object* v_attr_1680_; lean_object* v_asyncMode_1681_; uint8_t v___x_1682_; 
v_ext_1678_ = lean_ctor_get(v_attr_1629_, 1);
v_toEnvExtension_1679_ = lean_ctor_get(v_ext_1678_, 0);
v_attr_1680_ = lean_ctor_get(v_attr_1629_, 0);
v_asyncMode_1681_ = lean_ctor_get(v_toEnvExtension_1679_, 2);
lean_inc(v_decl_1630_);
lean_inc_ref(v_env_1674_);
v___x_1682_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_1674_, v_decl_1630_, v_asyncMode_1681_);
if (v___x_1682_ == 0)
{
lean_object* v_toAttributeImplCore_1683_; lean_object* v_name_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc_ref(v_attr_1680_);
lean_dec_ref(v_attr_1629_);
v_toAttributeImplCore_1683_ = lean_ctor_get(v_attr_1680_, 0);
lean_inc_ref(v_toAttributeImplCore_1683_);
lean_dec_ref(v_attr_1680_);
v_name_1684_ = lean_ctor_get(v_toAttributeImplCore_1683_, 1);
lean_inc(v_name_1684_);
lean_dec_ref(v_toAttributeImplCore_1683_);
v___x_1685_ = l_Lean_Environment_asyncPrefix_x3f(v_env_1674_);
v___x_1686_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_1684_, v_decl_1630_, v___x_1685_, v___y_1676_, v___y_1677_);
return v___x_1686_;
}
else
{
lean_dec_ref(v_env_1674_);
v___y_1651_ = v___y_1677_;
goto v___jp_1650_;
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_1629_ = stack[0].m_obj;
lean_object* v_decl_1630_ = stack[1].m_obj;
lean_object* v___y_1631_ = stack[2].m_obj;
lean_object* v___y_1632_ = stack[3].m_obj;
lean_object* v_res_1692_;
v_res_1692_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1629_, v_decl_1630_, v___y_1631_, v___y_1632_);
stack->m_obj
 = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___boxed(lean_object* v_attr_1693_, lean_object* v_decl_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v_attr_1693_, v_decl_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1698_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(lean_object* v_declName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
lean_inc(v_declName_1699_);
v___x_1703_ = l_Lean_validateDefEqAttr(v_declName_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = l_Lean_backwardDefeqAttr;
v___x_1705_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0(v___x_1704_, v_declName_1699_, v___y_1700_, v___y_1701_);
return v___x_1705_;
}
else
{
lean_dec(v_declName_1699_);
return v___x_1703_;
}
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1699_ = stack[0].m_obj;
lean_object* v___y_1700_ = stack[1].m_obj;
lean_object* v___y_1701_ = stack[2].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1699_, v___y_1700_, v___y_1701_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_declName_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(v_declName_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1711_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___f_1722_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1723_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1724_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1725_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1726_ = 0;
v___x_1727_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_));
v___x_1728_ = 0;
v___x_1729_ = l_Lean_registerTagAttribute(v___x_1723_, v___x_1724_, v___f_1722_, v___x_1725_, v___x_1726_, v___x_1727_, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1730_;
v_res_1730_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1730_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2____boxed(lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_();
return v_res_1732_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_attrName_1734_, lean_object* v_declName_1735_, lean_object* v_asyncPrefix_x3f_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_1734_, v_declName_1735_, v_asyncPrefix_x3f_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1734_ = stack[1].m_obj;
lean_object* v_declName_1735_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_1736_ = stack[3].m_obj;
lean_object* v___y_1737_ = stack[4].m_obj;
lean_object* v___y_1738_ = stack[5].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_attrName_1734_, v_declName_1735_, v_asyncPrefix_x3f_1736_, v___y_1737_, v___y_1738_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_attrName_1743_, lean_object* v_declName_1744_, lean_object* v_asyncPrefix_x3f_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1742_, v_attrName_1743_, v_declName_1744_, v_asyncPrefix_x3f_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1749_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_1750_, lean_object* v_attrName_1751_, lean_object* v_declName_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_1751_, v_declName_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1751_ = stack[1].m_obj;
lean_object* v_declName_1752_ = stack[2].m_obj;
lean_object* v___y_1753_ = stack[3].m_obj;
lean_object* v___y_1754_ = stack[4].m_obj;
lean_object* v_res_1757_;
v_res_1757_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(lean_box(0), v_attrName_1751_, v_declName_1752_, v___y_1753_, v___y_1754_);
stack->m_obj
 = v_res_1757_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_attrName_1759_, lean_object* v_declName_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_1758_, v_attrName_1759_, v_declName_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1764_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1768_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0));
v___x_1769_ = l_Lean_addBuiltinDocString(v___x_1767_, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1770_;
v_res_1770_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
return v_res_1772_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2_));
v___x_1800_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6));
v___x_1801_ = l_Lean_addBuiltinDeclarationRanges(v___x_1799_, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1802_;
v_res_1802_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
return v_res_1804_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* v_type_1816_, lean_object* v_proof_1817_, lean_object* v_a_1818_){
_start:
{
if (lean_obj_tag(v_type_1816_) == 7)
{
if (lean_obj_tag(v_proof_1817_) == 6)
{
lean_object* v_body_1820_; lean_object* v_body_1821_; 
v_body_1820_ = lean_ctor_get(v_type_1816_, 2);
v_body_1821_ = lean_ctor_get(v_proof_1817_, 2);
lean_inc_ref(v_body_1821_);
lean_dec_ref_known(v_proof_1817_, 3);
v_type_1816_ = v_body_1820_;
v_proof_1817_ = v_body_1821_;
goto _start;
}
else
{
uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref(v_proof_1817_);
v___x_1823_ = 0;
v___x_1824_ = lean_box(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1));
v___x_1827_ = lean_unsigned_to_nat(3u);
v___x_1828_ = l_Lean_Expr_isAppOfArity(v_type_1816_, v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_proof_1817_);
v___x_1829_ = lean_box(v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1));
v___x_1832_ = lean_unsigned_to_nat(2u);
v___x_1833_ = l_Lean_Expr_isAppOfArity(v_proof_1817_, v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3));
v___x_1835_ = l_Lean_Expr_isAppOfArity(v_proof_1817_, v___x_1834_, v___x_1832_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5));
v___x_1837_ = lean_unsigned_to_nat(4u);
v___x_1838_ = l_Lean_Expr_isAppOfArity(v_proof_1817_, v___x_1836_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = l_Lean_Expr_getAppFn(v_proof_1817_);
lean_dec_ref(v_proof_1817_);
v___x_1840_ = l_Lean_Expr_isConst(v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref(v___x_1839_);
v___x_1841_ = lean_box(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v_env_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1843_ = lean_st_ref_get(v_a_1818_);
v_env_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref_n(v_env_1844_, 2);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_Expr_constName_x21(v___x_1839_);
lean_dec_ref(v___x_1839_);
v___x_1846_ = l_Lean_defeqAttr;
lean_inc(v___x_1845_);
v___x_1847_ = l_Lean_TagAttribute_hasTag(v___x_1846_, v_env_1844_, v___x_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = l_Lean_backwardDefeqAttr;
v___x_1849_ = l_Lean_TagAttribute_hasTag(v___x_1848_, v_env_1844_, v___x_1845_);
v___x_1850_ = lean_box(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v___x_1845_);
lean_dec_ref(v_env_1844_);
v___x_1852_ = lean_box(v___x_1828_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Expr_appArg_x21(v_proof_1817_);
lean_dec_ref(v_proof_1817_);
v_proof_1817_ = v___x_1854_;
goto _start;
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec_ref(v_proof_1817_);
v___x_1856_ = lean_box(v___x_1828_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_proof_1817_);
v___x_1858_ = lean_box(v___x_1828_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1816_ = stack[0].m_obj;
lean_object* v_proof_1817_ = stack[1].m_obj;
lean_object* v_a_1818_ = stack[2].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1816_, v_proof_1817_, v_a_1818_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* v_type_1861_, lean_object* v_proof_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1861_, v_proof_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_type_1861_);
return v_res_1865_;
}
}
lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* v_type_1866_, lean_object* v_proof_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v_type_1866_, v_proof_1867_, v_a_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT void l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1866_ = stack[0].m_obj;
lean_object* v_proof_1867_ = stack[1].m_obj;
lean_object* v_a_1868_ = stack[2].m_obj;
lean_object* v_a_1869_ = stack[3].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1866_, v_proof_1867_, v_a_1868_, v_a_1869_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* v_type_1873_, lean_object* v_proof_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(v_type_1873_, v_proof_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec_ref(v_type_1873_);
return v_res_1878_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(lean_object* v_attrName_1879_, lean_object* v_declName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1886_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1887_ = l_Lean_MessageData_ofName(v_attrName_1879_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = 0;
v___x_1892_ = l_Lean_MessageData_ofConstName(v_declName_1880_, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1890_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1895_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1896_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1879_ = stack[0].m_obj;
lean_object* v_declName_1880_ = stack[1].m_obj;
lean_object* v___y_1881_ = stack[2].m_obj;
lean_object* v___y_1882_ = stack[3].m_obj;
lean_object* v___y_1883_ = stack[4].m_obj;
lean_object* v___y_1884_ = stack[5].m_obj;
lean_object* v_res_1897_;
v_res_1897_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1879_, v_declName_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
stack->m_obj
 = v_res_1897_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(lean_object* v_attrName_1898_, lean_object* v_declName_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_1898_, v_declName_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(lean_object* v_attrName_1906_, lean_object* v_declName_1907_, lean_object* v_asyncPrefix_x3f_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___y_1915_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1908_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_MessageData_nil;
v___y_1915_ = v___x_1928_;
goto v___jp_1914_;
}
else
{
lean_object* v_val_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_val_1929_ = lean_ctor_get(v_asyncPrefix_x3f_1908_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v_asyncPrefix_x3f_1908_, 1);
v___x_1930_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
v___x_1931_ = l_Lean_MessageData_ofName(v_val_1929_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___y_1915_ = v___x_1934_;
goto v___jp_1914_;
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1916_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1917_ = l_Lean_MessageData_ofName(v_attrName_1906_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = 0;
v___x_1922_ = l_Lean_MessageData_ofConstName(v_declName_1907_, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___y_1915_);
v___x_1927_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_1926_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1927_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_1906_ = stack[0].m_obj;
lean_object* v_declName_1907_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_1908_ = stack[2].m_obj;
lean_object* v___y_1909_ = stack[3].m_obj;
lean_object* v___y_1910_ = stack[4].m_obj;
lean_object* v___y_1911_ = stack[5].m_obj;
lean_object* v___y_1912_ = stack[6].m_obj;
lean_object* v_res_1935_;
v_res_1935_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1906_, v_declName_1907_, v_asyncPrefix_x3f_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
stack->m_obj
 = v_res_1935_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(lean_object* v_attrName_1936_, lean_object* v_declName_1937_, lean_object* v_asyncPrefix_x3f_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_1936_, v_declName_1937_, v_asyncPrefix_x3f_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1944_;
}
}
lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(lean_object* v_attr_1945_, lean_object* v_decl_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___x_2007_; lean_object* v_env_2008_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___x_2023_; 
v___x_2007_ = lean_st_ref_get(v___y_1950_);
v_env_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc_ref(v_env_2008_);
lean_dec(v___x_2007_);
v___x_2023_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2008_, v_decl_1946_);
if (lean_obj_tag(v___x_2023_) == 0)
{
v___y_2010_ = v___y_1947_;
v___y_2011_ = v___y_1948_;
v___y_2012_ = v___y_1949_;
v___y_2013_ = v___y_1950_;
goto v___jp_2009_;
}
else
{
lean_object* v_attr_2024_; lean_object* v_toAttributeImplCore_2025_; lean_object* v_name_2026_; lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2023_, 1);
lean_dec_ref(v_env_2008_);
v_attr_2024_ = lean_ctor_get(v_attr_1945_, 0);
lean_inc_ref(v_attr_2024_);
lean_dec_ref(v_attr_1945_);
v_toAttributeImplCore_2025_ = lean_ctor_get(v_attr_2024_, 0);
lean_inc_ref(v_toAttributeImplCore_2025_);
lean_dec_ref(v_attr_2024_);
v_name_2026_ = lean_ctor_get(v_toAttributeImplCore_2025_, 1);
lean_inc(v_name_2026_);
lean_dec_ref(v_toAttributeImplCore_2025_);
v___x_2027_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_2026_, v_decl_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_2027_;
}
v___jp_1952_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_mctx_1968_; lean_object* v_zetaDeltaFVarIds_1969_; lean_object* v_postponed_1970_; lean_object* v_diag_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1982_; 
v___x_1964_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
v___x_1965_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1965_, 0, v___y_1963_);
lean_ctor_set(v___x_1965_, 1, v___y_1955_);
lean_ctor_set(v___x_1965_, 2, v___y_1959_);
lean_ctor_set(v___x_1965_, 3, v___y_1953_);
lean_ctor_set(v___x_1965_, 4, v___y_1956_);
lean_ctor_set(v___x_1965_, 5, v___x_1964_);
lean_ctor_set(v___x_1965_, 6, v___y_1958_);
lean_ctor_set(v___x_1965_, 7, v___y_1957_);
lean_ctor_set(v___x_1965_, 8, v___y_1960_);
lean_ctor_set(v___x_1965_, 9, v___y_1962_);
v___x_1966_ = lean_st_ref_put(v___y_1954_, v___x_1965_);
v___x_1967_ = lean_st_ref_take(v___y_1961_);
v_mctx_1968_ = lean_ctor_get(v___x_1967_, 0);
v_zetaDeltaFVarIds_1969_ = lean_ctor_get(v___x_1967_, 2);
v_postponed_1970_ = lean_ctor_get(v___x_1967_, 3);
v_diag_1971_ = lean_ctor_get(v___x_1967_, 4);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1967_, 1);
lean_dec(v_unused_1983_);
v___x_1973_ = v___x_1967_;
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_diag_1971_);
lean_inc(v_postponed_1970_);
lean_inc(v_zetaDeltaFVarIds_1969_);
lean_inc(v_mctx_1968_);
lean_dec(v___x_1967_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___x_1976_);
v___x_1978_ = v___x_1973_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_mctx_1968_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_zetaDeltaFVarIds_1969_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_postponed_1970_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_diag_1971_);
v___x_1978_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_st_ref_put(v___y_1961_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1975_);
return v___x_1980_;
}
}
}
v___jp_1984_:
{
lean_object* v___x_1987_; lean_object* v_ext_1988_; lean_object* v_toEnvExtension_1989_; lean_object* v_env_1990_; lean_object* v_nextMacroScope_1991_; lean_object* v_ngen_1992_; lean_object* v_auxDeclNGen_1993_; lean_object* v_traceState_1994_; lean_object* v_recordedDeps_1995_; lean_object* v_messages_1996_; lean_object* v_infoState_1997_; lean_object* v_snapshotTasks_1998_; lean_object* v_addEntryFn_1999_; lean_object* v_asyncMode_2000_; uint8_t v_logWrites_2001_; lean_object* v___f_2002_; uint8_t v___x_2003_; 
v___x_1987_ = lean_st_ref_take(v___y_1986_);
v_ext_1988_ = lean_ctor_get(v_attr_1945_, 1);
lean_inc_ref(v_ext_1988_);
lean_dec_ref(v_attr_1945_);
v_toEnvExtension_1989_ = lean_ctor_get(v_ext_1988_, 0);
lean_inc_ref(v_toEnvExtension_1989_);
v_env_1990_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1990_);
v_nextMacroScope_1991_ = lean_ctor_get(v___x_1987_, 1);
lean_inc(v_nextMacroScope_1991_);
v_ngen_1992_ = lean_ctor_get(v___x_1987_, 2);
lean_inc_ref(v_ngen_1992_);
v_auxDeclNGen_1993_ = lean_ctor_get(v___x_1987_, 3);
lean_inc_ref(v_auxDeclNGen_1993_);
v_traceState_1994_ = lean_ctor_get(v___x_1987_, 4);
lean_inc_ref(v_traceState_1994_);
v_recordedDeps_1995_ = lean_ctor_get(v___x_1987_, 6);
lean_inc_ref(v_recordedDeps_1995_);
v_messages_1996_ = lean_ctor_get(v___x_1987_, 7);
lean_inc_ref(v_messages_1996_);
v_infoState_1997_ = lean_ctor_get(v___x_1987_, 8);
lean_inc_ref(v_infoState_1997_);
v_snapshotTasks_1998_ = lean_ctor_get(v___x_1987_, 9);
lean_inc_ref(v_snapshotTasks_1998_);
lean_dec(v___x_1987_);
v_addEntryFn_1999_ = lean_ctor_get(v_ext_1988_, 3);
lean_inc(v_addEntryFn_1999_);
lean_dec_ref(v_ext_1988_);
v_asyncMode_2000_ = lean_ctor_get(v_toEnvExtension_1989_, 2);
lean_inc(v_asyncMode_2000_);
v_logWrites_2001_ = lean_ctor_get_uint8(v_toEnvExtension_1989_, sizeof(void*)*6);
lean_inc(v_decl_1946_);
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_585514292____hygCtx___hyg_2__spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2002_, 0, v_addEntryFn_1999_);
lean_closure_set(v___f_2002_, 1, v_decl_1946_);
v___x_2003_ = 1;
if (v_logWrites_2001_ == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1989_, v_env_1990_, v___f_2002_, v_asyncMode_2000_, v_decl_1946_, v___x_2003_);
lean_dec(v_asyncMode_2000_);
v___y_1953_ = v_auxDeclNGen_1993_;
v___y_1954_ = v___y_1986_;
v___y_1955_ = v_nextMacroScope_1991_;
v___y_1956_ = v_traceState_1994_;
v___y_1957_ = v_messages_1996_;
v___y_1958_ = v_recordedDeps_1995_;
v___y_1959_ = v_ngen_1992_;
v___y_1960_ = v_infoState_1997_;
v___y_1961_ = v___y_1985_;
v___y_1962_ = v_snapshotTasks_1998_;
v___y_1963_ = v___x_2004_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_inc_ref(v_toEnvExtension_1989_);
v___x_2005_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1989_, v_env_1990_);
lean_dec_ref(v_env_1990_);
v___x_2006_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1989_, v___x_2005_, v___f_2002_, v_asyncMode_2000_, v_decl_1946_, v___x_2003_);
lean_dec(v_asyncMode_2000_);
v___y_1953_ = v_auxDeclNGen_1993_;
v___y_1954_ = v___y_1986_;
v___y_1955_ = v_nextMacroScope_1991_;
v___y_1956_ = v_traceState_1994_;
v___y_1957_ = v_messages_1996_;
v___y_1958_ = v_recordedDeps_1995_;
v___y_1959_ = v_ngen_1992_;
v___y_1960_ = v_infoState_1997_;
v___y_1961_ = v___y_1985_;
v___y_1962_ = v_snapshotTasks_1998_;
v___y_1963_ = v___x_2006_;
goto v___jp_1952_;
}
}
v___jp_2009_:
{
lean_object* v_ext_2014_; lean_object* v_toEnvExtension_2015_; lean_object* v_attr_2016_; lean_object* v_asyncMode_2017_; uint8_t v___x_2018_; 
v_ext_2014_ = lean_ctor_get(v_attr_1945_, 1);
v_toEnvExtension_2015_ = lean_ctor_get(v_ext_2014_, 0);
v_attr_2016_ = lean_ctor_get(v_attr_1945_, 0);
v_asyncMode_2017_ = lean_ctor_get(v_toEnvExtension_2015_, 2);
lean_inc(v_decl_1946_);
lean_inc_ref(v_env_2008_);
v___x_2018_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2008_, v_decl_1946_, v_asyncMode_2017_);
if (v___x_2018_ == 0)
{
lean_object* v_toAttributeImplCore_2019_; lean_object* v_name_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc_ref(v_attr_2016_);
lean_dec_ref(v_attr_1945_);
v_toAttributeImplCore_2019_ = lean_ctor_get(v_attr_2016_, 0);
lean_inc_ref(v_toAttributeImplCore_2019_);
lean_dec_ref(v_attr_2016_);
v_name_2020_ = lean_ctor_get(v_toAttributeImplCore_2019_, 1);
lean_inc(v_name_2020_);
lean_dec_ref(v_toAttributeImplCore_2019_);
v___x_2021_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2008_);
v___x_2022_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_2020_, v_decl_1946_, v___x_2021_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2022_;
}
else
{
lean_dec_ref(v_env_2008_);
v___y_1985_ = v___y_2011_;
v___y_1986_ = v___y_2013_;
goto v___jp_1984_;
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_1945_ = stack[0].m_obj;
lean_object* v_decl_1946_ = stack[1].m_obj;
lean_object* v___y_1947_ = stack[2].m_obj;
lean_object* v___y_1948_ = stack[3].m_obj;
lean_object* v___y_1949_ = stack[4].m_obj;
lean_object* v___y_1950_ = stack[5].m_obj;
lean_object* v_res_2028_;
v_res_2028_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_1945_, v_decl_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
stack->m_obj
 = v_res_2028_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(lean_object* v_attr_2029_, lean_object* v_decl_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v_attr_2029_, v_decl_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(lean_object* v_msg_2037_, lean_object* v_declHint_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_env_2043_; uint8_t v___x_2044_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_st_ref_get(v___y_2039_);
v_env_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = l_Lean_Name_isAnonymous(v_declHint_2038_);
if (v___x_2044_ == 0)
{
uint8_t v_isExporting_2045_; 
v_isExporting_2045_ = lean_ctor_get_uint8(v_env_2043_, sizeof(void*)*13);
if (v_isExporting_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec_ref(v_env_2043_);
lean_dec(v_declHint_2038_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_msg_2037_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
lean_inc_ref(v_env_2043_);
v___x_2047_ = l_Lean_Environment_setExporting(v_env_2043_, v___x_2044_);
lean_inc(v_declHint_2038_);
lean_inc_ref(v___x_2047_);
v___x_2048_ = l_Lean_Environment_contains(v___x_2047_, v_declHint_2038_, v_isExporting_2045_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec_ref(v___x_2047_);
lean_dec_ref(v_env_2043_);
lean_dec(v_declHint_2038_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_msg_2037_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v_c_2057_; lean_object* v___x_2058_; 
v___x_2050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_2051_ = lean_unsigned_to_nat(32u);
v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
lean_dec_ref(v___x_2052_);
v___x_2053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_2054_ = l_Lean_Options_empty;
v___x_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2047_);
lean_ctor_set(v___x_2055_, 1, v___x_2050_);
lean_ctor_set(v___x_2055_, 2, v___x_2053_);
lean_ctor_set(v___x_2055_, 3, v___x_2054_);
lean_inc(v_declHint_2038_);
v___x_2056_ = l_Lean_MessageData_ofConstName(v_declHint_2038_, v___x_2044_);
v_c_2057_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2057_, 0, v___x_2055_);
lean_ctor_set(v_c_2057_, 1, v___x_2056_);
v___x_2058_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2043_, v_declHint_2038_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v_env_2043_);
lean_dec(v_declHint_2038_);
v___x_2059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v_c_2057_);
v___x_2061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = l_Lean_MessageData_note(v___x_2062_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_msg_2037_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
else
{
lean_object* v_val_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2122_; 
v_val_2066_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2068_ = v___x_2058_;
v_isShared_2069_ = v_isSharedCheck_2122_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_val_2066_);
lean_dec(v___x_2058_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2122_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_modules_2071_; lean_object* v_moduleNames_2072_; lean_object* v_mod_2073_; uint8_t v___y_2075_; uint8_t v___x_2105_; 
v___x_2070_ = l_Lean_Environment_header(v_env_2043_);
lean_dec_ref(v_env_2043_);
v_modules_2071_ = lean_ctor_get(v___x_2070_, 3);
lean_inc_ref(v_modules_2071_);
v_moduleNames_2072_ = lean_ctor_get(v___x_2070_, 4);
lean_inc_ref(v_moduleNames_2072_);
lean_dec_ref(v___x_2070_);
v_mod_2073_ = lean_array_get(v___x_2041_, v_moduleNames_2072_, v_val_2066_);
lean_dec_ref(v_moduleNames_2072_);
v___x_2105_ = l_Lean_isPrivateName(v_declHint_2038_);
lean_dec(v_declHint_2038_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = lean_array_get_size(v_modules_2071_);
v___x_2107_ = lean_nat_dec_lt(v_val_2066_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_dec_ref(v_modules_2071_);
lean_dec(v_val_2066_);
v___y_2075_ = v___x_2105_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2108_; lean_object* v_toImport_2109_; uint8_t v_isExported_2110_; 
v___x_2108_ = lean_array_fget(v_modules_2071_, v_val_2066_);
lean_dec(v_val_2066_);
lean_dec_ref(v_modules_2071_);
v_toImport_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc_ref(v_toImport_2109_);
lean_dec(v___x_2108_);
v_isExported_2110_ = lean_ctor_get_uint8(v_toImport_2109_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2109_);
v___y_2075_ = v_isExported_2110_;
goto v___jp_2074_;
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_modules_2071_);
lean_del_object(v___x_2068_);
lean_dec(v_val_2066_);
v___x_2111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v_c_2057_);
v___x_2113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__24);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_Lean_MessageData_ofName(v_mod_2073_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__26);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_MessageData_note(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_msg_2037_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
v___jp_2074_:
{
if (v___y_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v_c_2057_);
v___x_2078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Lean_MessageData_ofName(v_mod_2073_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_MessageData_note(v___x_2083_);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_msg_2037_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2085_);
v___x_2087_ = v___x_2068_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_c_2057_);
v___x_2091_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_MessageData_ofName(v_mod_2073_);
lean_inc_ref(v___x_2093_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__20);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2093_);
v___x_2098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__22);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = l_Lean_MessageData_note(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_msg_2037_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2101_);
v___x_2103_ = v___x_2068_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
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
lean_object* v___x_2123_; 
lean_dec_ref(v_env_2043_);
lean_dec(v_declHint_2038_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_msg_2037_);
return v___x_2123_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2037_ = stack[0].m_obj;
lean_object* v_declHint_2038_ = stack[1].m_obj;
lean_object* v___y_2039_ = stack[2].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_2037_, v_declHint_2038_, v___y_2039_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_msg_2125_, lean_object* v_declHint_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_2125_, v_declHint_2126_, v___y_2127_);
lean_dec(v___y_2127_);
return v_res_2129_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(lean_object* v_msg_2130_, lean_object* v_declHint_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2147_; 
v___x_2137_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_2130_, v_declHint_2131_, v___y_2135_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2142_ = l_Lean_unknownIdentifierMessageTag;
v___x_2143_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_a_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2143_);
v___x_2145_ = v___x_2140_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2130_ = stack[0].m_obj;
lean_object* v_declHint_2131_ = stack[1].m_obj;
lean_object* v___y_2132_ = stack[2].m_obj;
lean_object* v___y_2133_ = stack[3].m_obj;
lean_object* v___y_2134_ = stack[4].m_obj;
lean_object* v___y_2135_ = stack[5].m_obj;
lean_object* v_res_2148_;
v_res_2148_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_2130_, v_declHint_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
stack->m_obj
 = v_res_2148_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(lean_object* v_msg_2149_, lean_object* v_declHint_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_2149_, v_declHint_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2156_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(lean_object* v_ref_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_toCold_2164_; lean_object* v_currRecDepth_2165_; lean_object* v_ref_2166_; uint16_t v_optionFlags_2167_; uint8_t v_suppressElabErrors_2168_; uint8_t v_isRecordingDeps_2169_; lean_object* v_ref_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_toCold_2164_ = lean_ctor_get(v___y_2161_, 0);
v_currRecDepth_2165_ = lean_ctor_get(v___y_2161_, 1);
v_ref_2166_ = lean_ctor_get(v___y_2161_, 2);
v_optionFlags_2167_ = lean_ctor_get_uint16(v___y_2161_, sizeof(void*)*3);
v_suppressElabErrors_2168_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2169_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*3 + 3);
v_ref_2170_ = l_Lean_replaceRef(v_ref_2157_, v_ref_2166_);
lean_inc(v_currRecDepth_2165_);
lean_inc_ref(v_toCold_2164_);
v___x_2171_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2171_, 0, v_toCold_2164_);
lean_ctor_set(v___x_2171_, 1, v_currRecDepth_2165_);
lean_ctor_set(v___x_2171_, 2, v_ref_2170_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3, v_optionFlags_2167_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 2, v_suppressElabErrors_2168_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 3, v_isRecordingDeps_2169_);
v___x_2172_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___x_2171_, v___y_2162_);
lean_dec_ref_known(v___x_2171_, 3);
return v___x_2172_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2157_ = stack[0].m_obj;
lean_object* v_msg_2158_ = stack[1].m_obj;
lean_object* v___y_2159_ = stack[2].m_obj;
lean_object* v___y_2160_ = stack[3].m_obj;
lean_object* v___y_2161_ = stack[4].m_obj;
lean_object* v___y_2162_ = stack[5].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2157_, v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_ref_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_ref_2174_);
return v_res_2181_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(lean_object* v_ref_2182_, lean_object* v_msg_2183_, lean_object* v_declHint_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v_a_2191_; lean_object* v___x_2192_; 
v___x_2190_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_2183_, v_declHint_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2182_, v_a_2191_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2192_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2182_ = stack[0].m_obj;
lean_object* v_msg_2183_ = stack[1].m_obj;
lean_object* v_declHint_2184_ = stack[2].m_obj;
lean_object* v___y_2185_ = stack[3].m_obj;
lean_object* v___y_2186_ = stack[4].m_obj;
lean_object* v___y_2187_ = stack[5].m_obj;
lean_object* v___y_2188_ = stack[6].m_obj;
lean_object* v_res_2193_;
v_res_2193_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2182_, v_msg_2183_, v_declHint_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
stack->m_obj
 = v_res_2193_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v_declHint_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2194_, v_msg_2195_, v_declHint_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v_ref_2194_);
return v_res_2202_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(lean_object* v_ref_2203_, lean_object* v_constName_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2210_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_2211_ = 0;
lean_inc(v_constName_2204_);
v___x_2212_ = l_Lean_MessageData_ofConstName(v_constName_2204_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2210_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2203_, v___x_2215_, v_constName_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2216_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2203_ = stack[0].m_obj;
lean_object* v_constName_2204_ = stack[1].m_obj;
lean_object* v___y_2205_ = stack[2].m_obj;
lean_object* v___y_2206_ = stack[3].m_obj;
lean_object* v___y_2207_ = stack[4].m_obj;
lean_object* v___y_2208_ = stack[5].m_obj;
lean_object* v_res_2217_;
v_res_2217_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2203_, v_constName_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
stack->m_obj
 = v_res_2217_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(lean_object* v_ref_2218_, lean_object* v_constName_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2218_, v_constName_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v_ref_2218_);
return v_res_2225_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(lean_object* v_constName_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_ref_2232_; lean_object* v___x_2233_; 
v_ref_2232_ = lean_ctor_get(v___y_2229_, 2);
v___x_2233_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2232_, v_constName_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2226_ = stack[0].m_obj;
lean_object* v___y_2227_ = stack[1].m_obj;
lean_object* v___y_2228_ = stack[2].m_obj;
lean_object* v___y_2229_ = stack[3].m_obj;
lean_object* v___y_2230_ = stack[4].m_obj;
lean_object* v_res_2234_;
v_res_2234_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
stack->m_obj
 = v_res_2234_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(lean_object* v_constName_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(lean_object* v_constName_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_env_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2248_ = lean_st_ref_get(v___y_2246_);
v_env_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_env_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = 0;
lean_inc(v_constName_2242_);
v___x_2251_ = l_Lean_Environment_find_x3f(v_env_2249_, v_constName_2242_, v___x_2250_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2252_;
}
else
{
lean_object* v_val_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_constName_2242_);
v_val_2253_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_val_2253_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 0);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_val_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2242_ = stack[0].m_obj;
lean_object* v___y_2243_ = stack[1].m_obj;
lean_object* v___y_2244_ = stack[2].m_obj;
lean_object* v___y_2245_ = stack[3].m_obj;
lean_object* v___y_2246_ = stack[4].m_obj;
lean_object* v_res_2261_;
v_res_2261_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(lean_object* v_constName_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_constName_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2268_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(lean_object* v_opts_2269_, lean_object* v_opt_2270_){
_start:
{
lean_object* v_name_2271_; lean_object* v_defValue_2272_; lean_object* v_map_2273_; lean_object* v___x_2274_; 
v_name_2271_ = lean_ctor_get(v_opt_2270_, 0);
v_defValue_2272_ = lean_ctor_get(v_opt_2270_, 1);
v_map_2273_ = lean_ctor_get(v_opts_2269_, 0);
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2273_, v_name_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_unbox(v_defValue_2272_);
return v___x_2275_;
}
else
{
lean_object* v_val_2276_; 
v_val_2276_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v___x_2274_, 1);
if (lean_obj_tag(v_val_2276_) == 1)
{
uint8_t v_v_2277_; 
v_v_2277_ = lean_ctor_get_uint8(v_val_2276_, 0);
lean_dec_ref_known(v_val_2276_, 0);
return v_v_2277_;
}
else
{
uint8_t v___x_2278_; 
lean_dec(v_val_2276_);
v___x_2278_ = lean_unbox(v_defValue_2272_);
return v___x_2278_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2269_ = stack[0].m_obj;
lean_object* v_opt_2270_ = stack[1].m_obj;
uint8_t v_res_2279_;
v_res_2279_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(v_opts_2269_, v_opt_2270_);
stack->m_num = v_res_2279_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10___boxed(lean_object* v_opts_2280_, lean_object* v_opt_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(v_opts_2280_, v_opt_2281_);
lean_dec_ref(v_opt_2281_);
lean_dec_ref(v_opts_2280_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_2291_, uint8_t v___y_2292_, lean_object* v_x_2293_){
_start:
{
if (lean_obj_tag(v_x_2293_) == 1)
{
lean_object* v_pre_2294_; 
v_pre_2294_ = lean_ctor_get(v_x_2293_, 0);
switch(lean_obj_tag(v_pre_2294_))
{
case 1:
{
lean_object* v_pre_2295_; 
v_pre_2295_ = lean_ctor_get(v_pre_2294_, 0);
switch(lean_obj_tag(v_pre_2295_))
{
case 0:
{
lean_object* v_str_2296_; lean_object* v_str_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_str_2296_ = lean_ctor_get(v_x_2293_, 1);
v_str_2297_ = lean_ctor_get(v_pre_2294_, 1);
v___x_2298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0));
v___x_2299_ = lean_string_dec_eq(v_str_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1));
v___x_2301_ = lean_string_dec_eq(v_str_2297_, v___x_2300_);
if (v___x_2301_ == 0)
{
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2));
v___x_2303_ = lean_string_dec_eq(v_str_2296_, v___x_2302_);
if (v___x_2303_ == 0)
{
return v___x_2303_;
}
else
{
return v_suppressElabErrors_2291_;
}
}
}
else
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3));
v___x_2305_ = lean_string_dec_eq(v_str_2296_, v___x_2304_);
if (v___x_2305_ == 0)
{
return v___x_2305_;
}
else
{
return v_suppressElabErrors_2291_;
}
}
}
case 1:
{
lean_object* v_pre_2306_; 
v_pre_2306_ = lean_ctor_get(v_pre_2295_, 0);
if (lean_obj_tag(v_pre_2306_) == 0)
{
lean_object* v_str_2307_; lean_object* v_str_2308_; lean_object* v_str_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_str_2307_ = lean_ctor_get(v_x_2293_, 1);
v_str_2308_ = lean_ctor_get(v_pre_2294_, 1);
v_str_2309_ = lean_ctor_get(v_pre_2295_, 1);
v___x_2310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4));
v___x_2311_ = lean_string_dec_eq(v_str_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5));
v___x_2313_ = lean_string_dec_eq(v_str_2308_, v___x_2312_);
if (v___x_2313_ == 0)
{
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6));
v___x_2315_ = lean_string_dec_eq(v_str_2307_, v___x_2314_);
if (v___x_2315_ == 0)
{
return v___x_2315_;
}
else
{
return v_suppressElabErrors_2291_;
}
}
}
}
else
{
return v___y_2292_;
}
}
default: 
{
return v___y_2292_;
}
}
}
case 0:
{
lean_object* v_str_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_str_2316_ = lean_ctor_get(v_x_2293_, 1);
v___x_2317_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1_spec__1___closed__0));
v___x_2318_ = lean_string_dec_eq(v_str_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
return v___x_2318_;
}
else
{
return v_suppressElabErrors_2291_;
}
}
default: 
{
return v___y_2292_;
}
}
}
else
{
return v___y_2292_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2291_ = stack[0].m_num;
uint8_t v___y_2292_ = stack[1].m_num;
lean_object* v_x_2293_ = stack[2].m_obj;
uint8_t v_res_2319_;
v_res_2319_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v_suppressElabErrors_2291_, v___y_2292_, v_x_2293_);
stack->m_num = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_2320_, lean_object* v___y_2321_, lean_object* v_x_2322_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2323_; uint8_t v___y_8992__boxed_2324_; uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_suppressElabErrors_boxed_2323_ = lean_unbox(v_suppressElabErrors_2320_);
v___y_8992__boxed_2324_ = lean_unbox(v___y_2321_);
v_res_2325_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_2323_, v___y_8992__boxed_2324_, v_x_2322_);
lean_dec(v_x_2322_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(lean_object* v_ref_2328_, lean_object* v_msgData_2329_, uint8_t v_severity_2330_, uint8_t v_isSilent_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v_toCold_2345_; lean_object* v___y_2346_; lean_object* v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; uint8_t v___y_2407_; lean_object* v___y_2408_; uint8_t v___y_2412_; uint8_t v___y_2413_; uint8_t v___y_2414_; uint8_t v___x_2425_; uint8_t v___y_2427_; uint8_t v___y_2428_; uint8_t v___y_2429_; uint8_t v___y_2431_; uint8_t v___x_2439_; 
v___x_2425_ = 2;
v___x_2439_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2330_, v___x_2425_);
if (v___x_2439_ == 0)
{
v___y_2431_ = v___x_2439_;
goto v___jp_2430_;
}
else
{
uint8_t v___x_2440_; 
lean_inc_ref(v_msgData_2329_);
v___x_2440_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2329_);
v___y_2431_ = v___x_2440_;
goto v___jp_2430_;
}
v___jp_2337_:
{
lean_object* v_currNamespace_2347_; lean_object* v_openDecls_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_env_2353_; lean_object* v_nextMacroScope_2354_; lean_object* v_ngen_2355_; lean_object* v_auxDeclNGen_2356_; lean_object* v_traceState_2357_; lean_object* v_cache_2358_; lean_object* v_recordedDeps_2359_; lean_object* v_messages_2360_; lean_object* v_infoState_2361_; lean_object* v_snapshotTasks_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2373_; 
v_currNamespace_2347_ = lean_ctor_get(v_toCold_2345_, 4);
v_openDecls_2348_ = lean_ctor_get(v_toCold_2345_, 5);
lean_inc(v_openDecls_2348_);
lean_inc(v_currNamespace_2347_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_currNamespace_2347_);
lean_ctor_set(v___x_2349_, 1, v_openDecls_2348_);
v___x_2350_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___y_2344_);
lean_inc_ref(v___y_2340_);
lean_inc_ref(v___y_2339_);
v___x_2351_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2351_, 0, v___y_2339_);
lean_ctor_set(v___x_2351_, 1, v___y_2342_);
lean_ctor_set(v___x_2351_, 2, v___y_2343_);
lean_ctor_set(v___x_2351_, 3, v___y_2340_);
lean_ctor_set(v___x_2351_, 4, v___x_2350_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*5, v___y_2338_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*5 + 1, v___y_2341_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*5 + 2, v_isSilent_2331_);
v___x_2352_ = lean_st_ref_take(v___y_2346_);
v_env_2353_ = lean_ctor_get(v___x_2352_, 0);
v_nextMacroScope_2354_ = lean_ctor_get(v___x_2352_, 1);
v_ngen_2355_ = lean_ctor_get(v___x_2352_, 2);
v_auxDeclNGen_2356_ = lean_ctor_get(v___x_2352_, 3);
v_traceState_2357_ = lean_ctor_get(v___x_2352_, 4);
v_cache_2358_ = lean_ctor_get(v___x_2352_, 5);
v_recordedDeps_2359_ = lean_ctor_get(v___x_2352_, 6);
v_messages_2360_ = lean_ctor_get(v___x_2352_, 7);
v_infoState_2361_ = lean_ctor_get(v___x_2352_, 8);
v_snapshotTasks_2362_ = lean_ctor_get(v___x_2352_, 9);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2373_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_snapshotTasks_2362_);
lean_inc(v_infoState_2361_);
lean_inc(v_messages_2360_);
lean_inc(v_recordedDeps_2359_);
lean_inc(v_cache_2358_);
lean_inc(v_traceState_2357_);
lean_inc(v_auxDeclNGen_2356_);
lean_inc(v_ngen_2355_);
lean_inc(v_nextMacroScope_2354_);
lean_inc(v_env_2353_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2373_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = l_Lean_MessageLog_add(v___x_2351_, v_messages_2360_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 7, v___x_2367_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_env_2353_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_nextMacroScope_2354_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_ngen_2355_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_auxDeclNGen_2356_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v_traceState_2357_);
lean_ctor_set(v_reuseFailAlloc_2372_, 5, v_cache_2358_);
lean_ctor_set(v_reuseFailAlloc_2372_, 6, v_recordedDeps_2359_);
lean_ctor_set(v_reuseFailAlloc_2372_, 7, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2372_, 8, v_infoState_2361_);
lean_ctor_set(v_reuseFailAlloc_2372_, 9, v_snapshotTasks_2362_);
v___x_2369_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_st_ref_put(v___y_2346_, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2366_);
return v___x_2371_;
}
}
}
v___jp_2374_:
{
lean_object* v_fileName_2383_; lean_object* v_fileMap_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2400_; 
v_fileName_2383_ = lean_ctor_get(v___y_2379_, 0);
v_fileMap_2384_ = lean_ctor_get(v___y_2379_, 1);
v___x_2385_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2329_);
v___x_2386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_2385_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2400_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2400_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc_ref_n(v_fileMap_2384_, 2);
v___x_2391_ = l_Lean_FileMap_toPosition(v_fileMap_2384_, v___y_2381_);
lean_dec(v___y_2381_);
v___x_2392_ = l_Lean_FileMap_toPosition(v_fileMap_2384_, v___y_2382_);
lean_dec(v___y_2382_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0));
if (v___y_2377_ == 0)
{
lean_del_object(v___x_2389_);
lean_dec_ref(v___y_2376_);
v___y_2338_ = v___y_2378_;
v___y_2339_ = v_fileName_2383_;
v___y_2340_ = v___x_2394_;
v___y_2341_ = v___y_2380_;
v___y_2342_ = v___x_2391_;
v___y_2343_ = v___x_2393_;
v___y_2344_ = v_a_2387_;
v_toCold_2345_ = v___y_2375_;
v___y_2346_ = v___y_2335_;
goto v___jp_2337_;
}
else
{
uint8_t v___x_2395_; 
lean_inc(v_a_2387_);
v___x_2395_ = l_Lean_MessageData_hasTag(v___y_2376_, v_a_2387_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_dec_ref_known(v___x_2393_, 1);
lean_dec_ref(v___x_2391_);
lean_dec(v_a_2387_);
v___x_2396_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2396_);
v___x_2398_ = v___x_2389_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
else
{
lean_del_object(v___x_2389_);
v___y_2338_ = v___y_2378_;
v___y_2339_ = v_fileName_2383_;
v___y_2340_ = v___x_2394_;
v___y_2341_ = v___y_2380_;
v___y_2342_ = v___x_2391_;
v___y_2343_ = v___x_2393_;
v___y_2344_ = v_a_2387_;
v_toCold_2345_ = v___y_2375_;
v___y_2346_ = v___y_2335_;
goto v___jp_2337_;
}
}
}
}
v___jp_2401_:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Syntax_getTailPos_x3f(v___y_2405_, v___y_2406_);
lean_dec(v___y_2405_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_inc(v___y_2408_);
v___y_2375_ = v___y_2403_;
v___y_2376_ = v___y_2404_;
v___y_2377_ = v___y_2402_;
v___y_2378_ = v___y_2406_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___y_2407_;
v___y_2381_ = v___y_2408_;
v___y_2382_ = v___y_2408_;
goto v___jp_2374_;
}
else
{
lean_object* v_val_2410_; 
v_val_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___y_2375_ = v___y_2403_;
v___y_2376_ = v___y_2404_;
v___y_2377_ = v___y_2402_;
v___y_2378_ = v___y_2406_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___y_2407_;
v___y_2381_ = v___y_2408_;
v___y_2382_ = v_val_2410_;
goto v___jp_2374_;
}
}
v___jp_2411_:
{
lean_object* v_toCold_2415_; lean_object* v_ref_2416_; uint8_t v_suppressElabErrors_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___f_2420_; lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_toCold_2415_ = lean_ctor_get(v___y_2334_, 0);
v_ref_2416_ = lean_ctor_get(v___y_2334_, 2);
v_suppressElabErrors_2417_ = lean_ctor_get_uint8(v___y_2334_, sizeof(void*)*3 + 2);
v___x_2418_ = lean_box(v_suppressElabErrors_2417_);
v___x_2419_ = lean_box(v___y_2412_);
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2420_, 0, v___x_2418_);
lean_closure_set(v___f_2420_, 1, v___x_2419_);
v_ref_2421_ = l_Lean_replaceRef(v_ref_2328_, v_ref_2416_);
v___x_2422_ = l_Lean_Syntax_getPos_x3f(v_ref_2421_, v___y_2413_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_unsigned_to_nat(0u);
v___y_2402_ = v_suppressElabErrors_2417_;
v___y_2403_ = v_toCold_2415_;
v___y_2404_ = v___f_2420_;
v___y_2405_ = v_ref_2421_;
v___y_2406_ = v___y_2413_;
v___y_2407_ = v___y_2414_;
v___y_2408_ = v___x_2423_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2424_; 
v_val_2424_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v___x_2422_, 1);
v___y_2402_ = v_suppressElabErrors_2417_;
v___y_2403_ = v_toCold_2415_;
v___y_2404_ = v___f_2420_;
v___y_2405_ = v_ref_2421_;
v___y_2406_ = v___y_2413_;
v___y_2407_ = v___y_2414_;
v___y_2408_ = v_val_2424_;
goto v___jp_2401_;
}
}
v___jp_2426_:
{
if (v___y_2429_ == 0)
{
v___y_2412_ = v___y_2427_;
v___y_2413_ = v___y_2428_;
v___y_2414_ = v_severity_2330_;
goto v___jp_2411_;
}
else
{
v___y_2412_ = v___y_2427_;
v___y_2413_ = v___y_2428_;
v___y_2414_ = v___x_2425_;
goto v___jp_2411_;
}
}
v___jp_2430_:
{
if (v___y_2431_ == 0)
{
uint8_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = 1;
v___x_2433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2330_, v___x_2432_);
if (v___x_2433_ == 0)
{
v___y_2427_ = v___y_2431_;
v___y_2428_ = v___y_2431_;
v___y_2429_ = v___x_2433_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2434_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2334_);
v___x_2435_ = l_Lean_warningAsError;
v___x_2436_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_spec__10(v___x_2434_, v___x_2435_);
lean_dec_ref(v___x_2434_);
v___y_2427_ = v___y_2431_;
v___y_2428_ = v___y_2431_;
v___y_2429_ = v___x_2436_;
goto v___jp_2426_;
}
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec_ref(v_msgData_2329_);
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2328_ = stack[0].m_obj;
lean_object* v_msgData_2329_ = stack[1].m_obj;
uint8_t v_severity_2330_ = stack[2].m_num;
uint8_t v_isSilent_2331_ = stack[3].m_num;
lean_object* v___y_2332_ = stack[4].m_obj;
lean_object* v___y_2333_ = stack[5].m_obj;
lean_object* v___y_2334_ = stack[6].m_obj;
lean_object* v___y_2335_ = stack[7].m_obj;
lean_object* v_res_2441_;
v_res_2441_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2328_, v_msgData_2329_, v_severity_2330_, v_isSilent_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
stack->m_obj
 = v_res_2441_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(lean_object* v_ref_2442_, lean_object* v_msgData_2443_, lean_object* v_severity_2444_, lean_object* v_isSilent_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v_severity_boxed_2451_; uint8_t v_isSilent_boxed_2452_; lean_object* v_res_2453_; 
v_severity_boxed_2451_ = lean_unbox(v_severity_2444_);
v_isSilent_boxed_2452_ = lean_unbox(v_isSilent_2445_);
v_res_2453_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2442_, v_msgData_2443_, v_severity_boxed_2451_, v_isSilent_boxed_2452_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v_ref_2442_);
return v_res_2453_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(lean_object* v_msgData_2454_, uint8_t v_severity_2455_, uint8_t v_isSilent_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_ref_2462_; lean_object* v___x_2463_; 
v_ref_2462_ = lean_ctor_get(v___y_2459_, 2);
v___x_2463_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_2462_, v_msgData_2454_, v_severity_2455_, v_isSilent_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2463_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2454_ = stack[0].m_obj;
uint8_t v_severity_2455_ = stack[1].m_num;
uint8_t v_isSilent_2456_ = stack[2].m_num;
lean_object* v___y_2457_ = stack[3].m_obj;
lean_object* v___y_2458_ = stack[4].m_obj;
lean_object* v___y_2459_ = stack[5].m_obj;
lean_object* v___y_2460_ = stack[6].m_obj;
lean_object* v_res_2464_;
v_res_2464_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2454_, v_severity_2455_, v_isSilent_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
stack->m_obj
 = v_res_2464_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(lean_object* v_msgData_2465_, lean_object* v_severity_2466_, lean_object* v_isSilent_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v_severity_boxed_2473_; uint8_t v_isSilent_boxed_2474_; lean_object* v_res_2475_; 
v_severity_boxed_2473_ = lean_unbox(v_severity_2466_);
v_isSilent_boxed_2474_ = lean_unbox(v_isSilent_2467_);
v_res_2475_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2465_, v_severity_boxed_2473_, v_isSilent_boxed_2474_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
return v_res_2475_;
}
}
lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(lean_object* v_msgData_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = 2;
v___x_2483_ = 0;
v___x_2484_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(v_msgData_2476_, v___x_2482_, v___x_2483_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2484_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2476_ = stack[0].m_obj;
lean_object* v___y_2477_ = stack[1].m_obj;
lean_object* v___y_2478_ = stack[2].m_obj;
lean_object* v___y_2479_ = stack[3].m_obj;
lean_object* v___y_2480_ = stack[4].m_obj;
lean_object* v_res_2485_;
v_res_2485_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
stack->m_obj
 = v_res_2485_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(lean_object* v_msgData_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v_msgData_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(lean_object* v___y_2493_, uint8_t v_isExporting_2494_, lean_object* v___x_2495_, lean_object* v___y_2496_, lean_object* v___x_2497_, lean_object* v_a_x3f_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v_env_2501_; lean_object* v_nextMacroScope_2502_; lean_object* v_ngen_2503_; lean_object* v_auxDeclNGen_2504_; lean_object* v_traceState_2505_; lean_object* v_recordedDeps_2506_; lean_object* v_messages_2507_; lean_object* v_infoState_2508_; lean_object* v_snapshotTasks_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2534_; 
v___x_2500_ = lean_st_ref_take(v___y_2493_);
v_env_2501_ = lean_ctor_get(v___x_2500_, 0);
v_nextMacroScope_2502_ = lean_ctor_get(v___x_2500_, 1);
v_ngen_2503_ = lean_ctor_get(v___x_2500_, 2);
v_auxDeclNGen_2504_ = lean_ctor_get(v___x_2500_, 3);
v_traceState_2505_ = lean_ctor_get(v___x_2500_, 4);
v_recordedDeps_2506_ = lean_ctor_get(v___x_2500_, 6);
v_messages_2507_ = lean_ctor_get(v___x_2500_, 7);
v_infoState_2508_ = lean_ctor_get(v___x_2500_, 8);
v_snapshotTasks_2509_ = lean_ctor_get(v___x_2500_, 9);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2500_, 5);
lean_dec(v_unused_2535_);
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2534_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snapshotTasks_2509_);
lean_inc(v_infoState_2508_);
lean_inc(v_messages_2507_);
lean_inc(v_recordedDeps_2506_);
lean_inc(v_traceState_2505_);
lean_inc(v_auxDeclNGen_2504_);
lean_inc(v_ngen_2503_);
lean_inc(v_nextMacroScope_2502_);
lean_inc(v_env_2501_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2534_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = l_Lean_Environment_setExporting(v_env_2501_, v_isExporting_2494_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 5, v___x_2495_);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_nextMacroScope_2502_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_ngen_2503_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_auxDeclNGen_2504_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_traceState_2505_);
lean_ctor_set(v_reuseFailAlloc_2533_, 5, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2533_, 6, v_recordedDeps_2506_);
lean_ctor_set(v_reuseFailAlloc_2533_, 7, v_messages_2507_);
lean_ctor_set(v_reuseFailAlloc_2533_, 8, v_infoState_2508_);
lean_ctor_set(v_reuseFailAlloc_2533_, 9, v_snapshotTasks_2509_);
v___x_2515_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_mctx_2518_; lean_object* v_zetaDeltaFVarIds_2519_; lean_object* v_postponed_2520_; lean_object* v_diag_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2531_; 
v___x_2516_ = lean_st_ref_put(v___y_2493_, v___x_2515_);
v___x_2517_ = lean_st_ref_take(v___y_2496_);
v_mctx_2518_ = lean_ctor_get(v___x_2517_, 0);
v_zetaDeltaFVarIds_2519_ = lean_ctor_get(v___x_2517_, 2);
v_postponed_2520_ = lean_ctor_get(v___x_2517_, 3);
v_diag_2521_ = lean_ctor_get(v___x_2517_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2517_, 1);
lean_dec(v_unused_2532_);
v___x_2523_ = v___x_2517_;
v_isShared_2524_ = v_isSharedCheck_2531_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_diag_2521_);
lean_inc(v_postponed_2520_);
lean_inc(v_zetaDeltaFVarIds_2519_);
lean_inc(v_mctx_2518_);
lean_dec(v___x_2517_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2531_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_box(0);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2497_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_mctx_2518_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_zetaDeltaFVarIds_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_postponed_2520_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_diag_2521_);
v___x_2527_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_st_ref_put(v___y_2496_, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2525_);
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2493_ = stack[0].m_obj;
uint8_t v_isExporting_2494_ = stack[1].m_num;
lean_object* v___x_2495_ = stack[2].m_obj;
lean_object* v___y_2496_ = stack[3].m_obj;
lean_object* v___x_2497_ = stack[4].m_obj;
lean_object* v_a_x3f_2498_ = stack[5].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2493_, v_isExporting_2494_, v___x_2495_, v___y_2496_, v___x_2497_, v_a_x3f_2498_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(lean_object* v___y_2537_, lean_object* v_isExporting_2538_, lean_object* v___x_2539_, lean_object* v___y_2540_, lean_object* v___x_2541_, lean_object* v_a_x3f_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v_isExporting_boxed_2544_; lean_object* v_res_2545_; 
v_isExporting_boxed_2544_ = lean_unbox(v_isExporting_2538_);
v_res_2545_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2537_, v_isExporting_boxed_2544_, v___x_2539_, v___y_2540_, v___x_2541_, v_a_x3f_2542_);
lean_dec(v_a_x3f_2542_);
lean_dec(v___y_2540_);
lean_dec(v___y_2537_);
return v_res_2545_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(lean_object* v_declName_2546_, uint8_t v_isExporting_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v_env_2553_; lean_object* v___x_2554_; uint8_t v_isModule_2555_; 
v___x_2552_ = lean_st_ref_get(v___y_2550_);
v_env_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref(v_env_2553_);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_Environment_header(v_env_2553_);
v_isModule_2555_ = lean_ctor_get_uint8(v___x_2554_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2554_);
if (v_isModule_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_dec_ref(v_env_2553_);
v___x_2556_ = l_Lean_validateDefEqAttr(v_declName_2546_, v___y_2549_, v___y_2550_);
return v___x_2556_;
}
else
{
uint8_t v_isExporting_2557_; 
v_isExporting_2557_ = lean_ctor_get_uint8(v_env_2553_, sizeof(void*)*13);
lean_dec_ref(v_env_2553_);
if (v_isExporting_2547_ == 0)
{
if (v_isExporting_2557_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_validateDefEqAttr(v_declName_2546_, v___y_2549_, v___y_2550_);
return v___x_2624_;
}
else
{
goto v___jp_2558_;
}
}
else
{
if (v_isExporting_2557_ == 0)
{
goto v___jp_2558_;
}
else
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_validateDefEqAttr(v_declName_2546_, v___y_2549_, v___y_2550_);
return v___x_2625_;
}
}
v___jp_2558_:
{
lean_object* v___x_2559_; lean_object* v_env_2560_; lean_object* v_nextMacroScope_2561_; lean_object* v_ngen_2562_; lean_object* v_auxDeclNGen_2563_; lean_object* v_traceState_2564_; lean_object* v_recordedDeps_2565_; lean_object* v_messages_2566_; lean_object* v_infoState_2567_; lean_object* v_snapshotTasks_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2622_; 
v___x_2559_ = lean_st_ref_take(v___y_2550_);
v_env_2560_ = lean_ctor_get(v___x_2559_, 0);
v_nextMacroScope_2561_ = lean_ctor_get(v___x_2559_, 1);
v_ngen_2562_ = lean_ctor_get(v___x_2559_, 2);
v_auxDeclNGen_2563_ = lean_ctor_get(v___x_2559_, 3);
v_traceState_2564_ = lean_ctor_get(v___x_2559_, 4);
v_recordedDeps_2565_ = lean_ctor_get(v___x_2559_, 6);
v_messages_2566_ = lean_ctor_get(v___x_2559_, 7);
v_infoState_2567_ = lean_ctor_get(v___x_2559_, 8);
v_snapshotTasks_2568_ = lean_ctor_get(v___x_2559_, 9);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v___x_2559_, 5);
lean_dec(v_unused_2623_);
v___x_2570_ = v___x_2559_;
v_isShared_2571_ = v_isSharedCheck_2622_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snapshotTasks_2568_);
lean_inc(v_infoState_2567_);
lean_inc(v_messages_2566_);
lean_inc(v_recordedDeps_2565_);
lean_inc(v_traceState_2564_);
lean_inc(v_auxDeclNGen_2563_);
lean_inc(v_ngen_2562_);
lean_inc(v_nextMacroScope_2561_);
lean_inc(v_env_2560_);
lean_dec(v___x_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2622_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = l_Lean_Environment_setExporting(v_env_2560_, v_isExporting_2547_);
v___x_2573_ = lean_obj_once(&l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2, &l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once, _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 5, v___x_2573_);
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_nextMacroScope_2561_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_ngen_2562_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_auxDeclNGen_2563_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_traceState_2564_);
lean_ctor_set(v_reuseFailAlloc_2621_, 5, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2621_, 6, v_recordedDeps_2565_);
lean_ctor_set(v_reuseFailAlloc_2621_, 7, v_messages_2566_);
lean_ctor_set(v_reuseFailAlloc_2621_, 8, v_infoState_2567_);
lean_ctor_set(v_reuseFailAlloc_2621_, 9, v_snapshotTasks_2568_);
v___x_2575_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_mctx_2578_; lean_object* v_zetaDeltaFVarIds_2579_; lean_object* v_postponed_2580_; lean_object* v_diag_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2619_; 
v___x_2576_ = lean_st_ref_put(v___y_2550_, v___x_2575_);
v___x_2577_ = lean_st_ref_take(v___y_2548_);
v_mctx_2578_ = lean_ctor_get(v___x_2577_, 0);
v_zetaDeltaFVarIds_2579_ = lean_ctor_get(v___x_2577_, 2);
v_postponed_2580_ = lean_ctor_get(v___x_2577_, 3);
v_diag_2581_ = lean_ctor_get(v___x_2577_, 4);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v___x_2577_, 1);
lean_dec(v_unused_2620_);
v___x_2583_ = v___x_2577_;
v_isShared_2584_ = v_isSharedCheck_2619_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_diag_2581_);
lean_inc(v_postponed_2580_);
lean_inc(v_zetaDeltaFVarIds_2579_);
lean_inc(v_mctx_2578_);
lean_dec(v___x_2577_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2619_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 1, v___x_2585_);
v___x_2587_ = v___x_2583_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_mctx_2578_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2585_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_zetaDeltaFVarIds_2579_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_postponed_2580_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_diag_2581_);
v___x_2587_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; lean_object* v_r_2589_; 
v___x_2588_ = lean_st_ref_put(v___y_2548_, v___x_2587_);
v_r_2589_ = l_Lean_validateDefEqAttr(v_declName_2546_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v_r_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2606_; 
v_a_2590_ = lean_ctor_get(v_r_2589_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2592_ = v_r_2589_;
v_isShared_2593_ = v_isSharedCheck_2606_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v_r_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2606_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
lean_inc(v_a_2590_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 1);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v___x_2596_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2550_, v_isExporting_2557_, v___x_2573_, v___y_2548_, v___x_2585_, v___x_2595_);
lean_dec_ref(v___x_2595_);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2596_, 0);
lean_dec(v_unused_2604_);
v___x_2598_ = v___x_2596_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_dec(v___x_2596_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_a_2590_);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2590_);
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
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2607_ = lean_ctor_get(v_r_2589_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v_r_2589_, 1);
v___x_2608_ = lean_box(0);
v___x_2609_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_2550_, v_isExporting_2557_, v___x_2573_, v___y_2548_, v___x_2585_, v___x_2608_);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v___x_2609_, 0);
lean_dec(v_unused_2617_);
v___x_2611_ = v___x_2609_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_dec(v___x_2609_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v_a_2607_);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2607_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2546_ = stack[0].m_obj;
uint8_t v_isExporting_2547_ = stack[1].m_num;
lean_object* v___y_2548_ = stack[2].m_obj;
lean_object* v___y_2549_ = stack[3].m_obj;
lean_object* v___y_2550_ = stack[4].m_obj;
lean_object* v_res_2626_;
v_res_2626_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2546_, v_isExporting_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
stack->m_obj
 = v_res_2626_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(lean_object* v_declName_2627_, lean_object* v_isExporting_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v_isExporting_boxed_2633_; lean_object* v_res_2634_; 
v_isExporting_boxed_2633_ = lean_unbox(v_isExporting_2628_);
v_res_2634_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2627_, v_isExporting_boxed_2633_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
return v_res_2634_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(lean_object* v_declName_2635_, uint8_t v_isExporting_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2635_, v_isExporting_2636_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2635_ = stack[0].m_obj;
uint8_t v_isExporting_2636_ = stack[1].m_num;
lean_object* v___y_2637_ = stack[2].m_obj;
lean_object* v___y_2638_ = stack[3].m_obj;
lean_object* v___y_2639_ = stack[4].m_obj;
lean_object* v___y_2640_ = stack[5].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2635_, v_isExporting_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(lean_object* v_declName_2644_, lean_object* v_isExporting_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v_isExporting_boxed_2651_; lean_object* v_res_2652_; 
v_isExporting_boxed_2651_ = lean_unbox(v_isExporting_2645_);
v_res_2652_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_2644_, v_isExporting_boxed_2651_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2652_;
}
}
lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* v_lhs_2653_, lean_object* v_rhs_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___y_2661_; lean_object* v___x_2678_; uint8_t v_transparency_2679_; uint8_t v___x_2680_; uint8_t v___x_2681_; 
v___x_2678_ = l_Lean_Meta_Context_config(v___y_2655_);
v_transparency_2679_ = lean_ctor_get_uint8(v___x_2678_, 9);
lean_dec_ref(v___x_2678_);
v___x_2680_ = 5;
v___x_2681_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v_keyedConfig_2682_; uint8_t v_trackZetaDelta_2683_; lean_object* v_zetaDeltaSet_2684_; lean_object* v_lctx_2685_; lean_object* v_localInstances_2686_; lean_object* v_defEqCtx_x3f_2687_; lean_object* v_synthPendingDepth_2688_; lean_object* v_customCanUnfoldPredicate_x3f_2689_; uint8_t v_univApprox_2690_; uint8_t v_inTypeClassResolution_2691_; uint8_t v_cacheInferType_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_keyedConfig_2682_ = lean_ctor_get(v___y_2655_, 0);
v_trackZetaDelta_2683_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7);
v_zetaDeltaSet_2684_ = lean_ctor_get(v___y_2655_, 1);
v_lctx_2685_ = lean_ctor_get(v___y_2655_, 2);
v_localInstances_2686_ = lean_ctor_get(v___y_2655_, 3);
v_defEqCtx_x3f_2687_ = lean_ctor_get(v___y_2655_, 4);
v_synthPendingDepth_2688_ = lean_ctor_get(v___y_2655_, 5);
v_customCanUnfoldPredicate_x3f_2689_ = lean_ctor_get(v___y_2655_, 6);
v_univApprox_2690_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2691_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 2);
v_cacheInferType_2692_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2682_);
v___x_2693_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2680_, v_keyedConfig_2682_);
lean_inc(v_customCanUnfoldPredicate_x3f_2689_);
lean_inc(v_synthPendingDepth_2688_);
lean_inc(v_defEqCtx_x3f_2687_);
lean_inc_ref(v_localInstances_2686_);
lean_inc_ref(v_lctx_2685_);
lean_inc(v_zetaDeltaSet_2684_);
v___x_2694_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_zetaDeltaSet_2684_);
lean_ctor_set(v___x_2694_, 2, v_lctx_2685_);
lean_ctor_set(v___x_2694_, 3, v_localInstances_2686_);
lean_ctor_set(v___x_2694_, 4, v_defEqCtx_x3f_2687_);
lean_ctor_set(v___x_2694_, 5, v_synthPendingDepth_2688_);
lean_ctor_set(v___x_2694_, 6, v_customCanUnfoldPredicate_x3f_2689_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*7, v_trackZetaDelta_2683_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*7 + 1, v_univApprox_2690_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2691_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*7 + 3, v_cacheInferType_2692_);
v___x_2695_ = l_Lean_Meta_isExprDefEq(v_lhs_2653_, v_rhs_2654_, v___x_2694_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec_ref_known(v___x_2694_, 7);
v___y_2661_ = v___x_2695_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_Meta_isExprDefEq(v_lhs_2653_, v_rhs_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
v___y_2661_ = v___x_2696_;
goto v___jp_2660_;
}
v___jp_2660_:
{
if (lean_obj_tag(v___y_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_a_2662_ = lean_ctor_get(v___y_2661_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___y_2661_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___y_2661_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___y_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v___y_2661_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___y_2661_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___y_2661_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___y_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_inferDefEqAttr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2653_ = stack[0].m_obj;
lean_object* v_rhs_2654_ = stack[1].m_obj;
lean_object* v___y_2655_ = stack[2].m_obj;
lean_object* v___y_2656_ = stack[3].m_obj;
lean_object* v___y_2657_ = stack[4].m_obj;
lean_object* v___y_2658_ = stack[5].m_obj;
lean_object* v_res_2697_;
v_res_2697_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2653_, v_rhs_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
stack->m_obj
 = v_res_2697_;
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* v_lhs_2698_, lean_object* v_rhs_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_inferDefEqAttr___lam__0(v_lhs_2698_, v_rhs_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__0));
v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
return v___x_2708_;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_inferDefEqAttr___lam__1___closed__2));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* v_declName_2712_, lean_object* v___f_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2725_; 
lean_inc(v_declName_2712_);
v___x_2725_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(v_declName_2712_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_n(v_a_2726_, 2);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = 1;
v___x_2728_ = l_Lean_ConstantInfo_value_x3f(v_a_2726_, v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 1)
{
lean_object* v_val_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_val_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_val_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = l_Lean_ConstantInfo_type(v_a_2726_);
lean_dec(v_a_2726_);
v___x_2731_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(v___x_2730_, v_val_2729_, v___y_2717_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; uint8_t v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = lean_unbox(v_a_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v_a_2732_);
lean_dec_ref(v___x_2730_);
lean_dec_ref(v___f_2713_);
lean_dec(v_declName_2712_);
goto v___jp_2722_;
}
else
{
lean_object* v___x_2734_; 
v___x_2734_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(v___x_2730_, v___f_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___y_2741_; lean_object* v___y_2743_; lean_object* v___y_2744_; uint8_t v___y_2745_; uint8_t v___y_2757_; uint8_t v___x_2762_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2762_ = l_Lean_isPrivateName(v_declName_2712_);
if (v___x_2762_ == 0)
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_unbox(v_a_2732_);
lean_dec(v_a_2732_);
v___y_2757_ = v___x_2763_;
goto v___jp_2756_;
}
else
{
uint8_t v___x_2764_; 
lean_dec(v_a_2732_);
v___x_2764_ = 0;
v___y_2757_ = v___x_2764_;
goto v___jp_2756_;
}
v___jp_2736_:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_unbox(v_a_2735_);
lean_dec(v_a_2735_);
if (v___x_2737_ == 0)
{
goto v___jp_2719_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = l_Lean_defeqAttr;
lean_inc(v_declName_2712_);
v___x_2739_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2738_, v_declName_2712_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_dec_ref_known(v___x_2739_, 1);
goto v___jp_2719_;
}
else
{
lean_dec(v_declName_2712_);
return v___x_2739_;
}
}
}
v___jp_2740_:
{
if (lean_obj_tag(v___y_2741_) == 0)
{
lean_dec_ref_known(v___y_2741_, 1);
goto v___jp_2736_;
}
else
{
lean_dec(v_a_2735_);
lean_dec(v_declName_2712_);
return v___y_2741_;
}
}
v___jp_2742_:
{
if (v___y_2745_ == 0)
{
uint8_t v___x_2746_; 
lean_dec_ref(v___y_2744_);
v___x_2746_ = lean_unbox(v_a_2735_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2747_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__1, &l_Lean_inferDefEqAttr___lam__1___closed__1_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__1);
lean_inc(v_declName_2712_);
v___x_2748_ = l_Lean_MessageData_ofName(v_declName_2712_);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_obj_once(&l_Lean_inferDefEqAttr___lam__1___closed__3, &l_Lean_inferDefEqAttr___lam__1___closed__3_once, _init_l_Lean_inferDefEqAttr___lam__1___closed__3);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_Exception_toMessageData(v___y_2743_);
v___x_2753_ = l_Lean_indentD(v___x_2752_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2751_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(v___x_2754_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
v___y_2741_ = v___x_2755_;
goto v___jp_2740_;
}
else
{
lean_dec_ref(v___y_2743_);
goto v___jp_2736_;
}
}
else
{
lean_dec_ref(v___y_2743_);
v___y_2741_ = v___y_2744_;
goto v___jp_2740_;
}
}
v___jp_2756_:
{
lean_object* v___x_2758_; 
lean_inc(v_declName_2712_);
v___x_2758_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_2712_, v___y_2757_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2758_) == 0)
{
v___y_2741_ = v___x_2758_;
goto v___jp_2740_;
}
else
{
lean_object* v_a_2759_; uint8_t v___x_2760_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
v___x_2760_ = l_Lean_Exception_isInterrupt(v_a_2759_);
if (v___x_2760_ == 0)
{
uint8_t v___x_2761_; 
lean_inc(v_a_2759_);
v___x_2761_ = l_Lean_Exception_isRuntime(v_a_2759_);
v___y_2743_ = v_a_2759_;
v___y_2744_ = v___x_2758_;
v___y_2745_ = v___x_2761_;
goto v___jp_2742_;
}
else
{
v___y_2743_ = v_a_2759_;
v___y_2744_ = v___x_2758_;
v___y_2745_ = v___x_2760_;
goto v___jp_2742_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_a_2732_);
lean_dec(v_declName_2712_);
v_a_2765_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2734_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2734_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v___x_2730_);
lean_dec_ref(v___f_2713_);
lean_dec(v_declName_2712_);
v_a_2773_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2731_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2731_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_dec(v___x_2728_);
lean_dec(v_a_2726_);
lean_dec_ref(v___f_2713_);
lean_dec(v_declName_2712_);
goto v___jp_2722_;
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v___f_2713_);
lean_dec(v_declName_2712_);
v_a_2781_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2725_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2725_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
v___jp_2719_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = l_Lean_backwardDefeqAttr;
v___x_2721_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(v___x_2720_, v_declName_2712_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2721_;
}
v___jp_2722_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
}
LEAN_EXPORT void l_Lean_inferDefEqAttr___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2712_ = stack[0].m_obj;
lean_object* v___f_2713_ = stack[1].m_obj;
lean_object* v___y_2714_ = stack[2].m_obj;
lean_object* v___y_2715_ = stack[3].m_obj;
lean_object* v___y_2716_ = stack[4].m_obj;
lean_object* v___y_2717_ = stack[5].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2712_, v___f_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
stack->m_obj
 = v_res_2789_;
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1___boxed(lean_object* v_declName_2790_, lean_object* v___f_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_inferDefEqAttr___lam__1(v_declName_2790_, v___f_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
return v_res_2797_;
}
}
lean_object* l_Lean_inferDefEqAttr(lean_object* v_declName_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___f_2805_; lean_object* v___f_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; 
v___f_2805_ = ((lean_object*)(l_Lean_inferDefEqAttr___closed__0));
v___f_2806_ = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1___boxed), 7, 2);
lean_closure_set(v___f_2806_, 0, v_declName_2799_);
lean_closure_set(v___f_2806_, 1, v___f_2805_);
v___x_2807_ = 1;
v___x_2808_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(v___f_2806_, v___x_2807_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
return v___x_2808_;
}
}
LEAN_EXPORT void l_Lean_inferDefEqAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2799_ = stack[0].m_obj;
lean_object* v_a_2800_ = stack[1].m_obj;
lean_object* v_a_2801_ = stack[2].m_obj;
lean_object* v_a_2802_ = stack[3].m_obj;
lean_object* v_a_2803_ = stack[4].m_obj;
lean_object* v_res_2809_;
v_res_2809_ = l_Lean_inferDefEqAttr(v_declName_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
stack->m_obj
 = v_res_2809_;
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___boxed(lean_object* v_declName_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_inferDefEqAttr(v_declName_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2816_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_object* v_00_u03b1_2817_, lean_object* v_attrName_2818_, lean_object* v_declName_2819_, lean_object* v_asyncPrefix_x3f_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_2818_, v_declName_2819_, v_asyncPrefix_x3f_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2818_ = stack[1].m_obj;
lean_object* v_declName_2819_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_2820_ = stack[3].m_obj;
lean_object* v___y_2821_ = stack[4].m_obj;
lean_object* v___y_2822_ = stack[5].m_obj;
lean_object* v___y_2823_ = stack[6].m_obj;
lean_object* v___y_2824_ = stack[7].m_obj;
lean_object* v_res_2827_;
v_res_2827_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(lean_box(0), v_attrName_2818_, v_declName_2819_, v_asyncPrefix_x3f_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
stack->m_obj
 = v_res_2827_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_attrName_2829_, lean_object* v_declName_2830_, lean_object* v_asyncPrefix_x3f_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_2828_, v_attrName_2829_, v_declName_2830_, v_asyncPrefix_x3f_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2837_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_object* v_00_u03b1_2838_, lean_object* v_attrName_2839_, lean_object* v_declName_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_2839_, v_declName_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2839_ = stack[1].m_obj;
lean_object* v_declName_2840_ = stack[2].m_obj;
lean_object* v___y_2841_ = stack[3].m_obj;
lean_object* v___y_2842_ = stack[4].m_obj;
lean_object* v___y_2843_ = stack[5].m_obj;
lean_object* v___y_2844_ = stack[6].m_obj;
lean_object* v_res_2847_;
v_res_2847_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(lean_box(0), v_attrName_2839_, v_declName_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
stack->m_obj
 = v_res_2847_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2848_, lean_object* v_attrName_2849_, lean_object* v_declName_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_2848_, v_attrName_2849_, v_declName_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
return v_res_2856_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_object* v_00_u03b1_2857_, lean_object* v_constName_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2858_ = stack[1].m_obj;
lean_object* v___y_2859_ = stack[2].m_obj;
lean_object* v___y_2860_ = stack[3].m_obj;
lean_object* v___y_2861_ = stack[4].m_obj;
lean_object* v___y_2862_ = stack[5].m_obj;
lean_object* v_res_2865_;
v_res_2865_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(lean_box(0), v_constName_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
stack->m_obj
 = v_res_2865_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2866_, lean_object* v_constName_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_2866_, v_constName_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2873_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_object* v_00_u03b1_2874_, lean_object* v_ref_2875_, lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_2875_, v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2875_ = stack[1].m_obj;
lean_object* v_constName_2876_ = stack[2].m_obj;
lean_object* v___y_2877_ = stack[3].m_obj;
lean_object* v___y_2878_ = stack[4].m_obj;
lean_object* v___y_2879_ = stack[5].m_obj;
lean_object* v___y_2880_ = stack[6].m_obj;
lean_object* v_res_2883_;
v_res_2883_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(lean_box(0), v_ref_2875_, v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
stack->m_obj
 = v_res_2883_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_ref_2885_, lean_object* v_constName_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_2884_, v_ref_2885_, v_constName_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v_ref_2885_);
return v_res_2892_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_object* v_00_u03b1_2893_, lean_object* v_ref_2894_, lean_object* v_msg_2895_, lean_object* v_declHint_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_2894_, v_msg_2895_, v_declHint_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2894_ = stack[1].m_obj;
lean_object* v_msg_2895_ = stack[2].m_obj;
lean_object* v_declHint_2896_ = stack[3].m_obj;
lean_object* v___y_2897_ = stack[4].m_obj;
lean_object* v___y_2898_ = stack[5].m_obj;
lean_object* v___y_2899_ = stack[6].m_obj;
lean_object* v___y_2900_ = stack[7].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(lean_box(0), v_ref_2894_, v_msg_2895_, v_declHint_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_ref_2905_, lean_object* v_msg_2906_, lean_object* v_declHint_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_2904_, v_ref_2905_, v_msg_2906_, v_declHint_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v_ref_2905_);
return v_res_2913_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(lean_object* v_msg_2914_, lean_object* v_declHint_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___redArg(v_msg_2914_, v_declHint_2915_, v___y_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2914_ = stack[0].m_obj;
lean_object* v_declHint_2915_ = stack[1].m_obj;
lean_object* v___y_2916_ = stack[2].m_obj;
lean_object* v___y_2917_ = stack[3].m_obj;
lean_object* v___y_2918_ = stack[4].m_obj;
lean_object* v___y_2919_ = stack[5].m_obj;
lean_object* v_res_2922_;
v_res_2922_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(v_msg_2914_, v_declHint_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
stack->m_obj
 = v_res_2922_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12___boxed(lean_object* v_msg_2923_, lean_object* v_declHint_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__12(v_msg_2923_, v_declHint_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_object* v_00_u03b1_2931_, lean_object* v_ref_2932_, lean_object* v_msg_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_2932_, v_msg_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2932_ = stack[1].m_obj;
lean_object* v_msg_2933_ = stack[2].m_obj;
lean_object* v___y_2934_ = stack[3].m_obj;
lean_object* v___y_2935_ = stack[4].m_obj;
lean_object* v___y_2936_ = stack[5].m_obj;
lean_object* v___y_2937_ = stack[6].m_obj;
lean_object* v_res_2940_;
v_res_2940_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(lean_box(0), v_ref_2932_, v_msg_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
stack->m_obj
 = v_res_2940_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2941_, lean_object* v_ref_2942_, lean_object* v_msg_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_2941_, v_ref_2942_, v_msg_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v_ref_2942_);
return v_res_2949_;
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
