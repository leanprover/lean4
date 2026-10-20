// Lean compiler output
// Module: Lean.Elab.Tactic.Rwa
// Imports: public import Lean.Elab.Tactic.Rewrite import Lean.Linter.Init import Lean.Meta.Tactic.TryThis
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unnecessaryRwa"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 240, 226, 220, 226, 178, 240, 85)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "enable the unnecessary `rwa` linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 218, 239, 141, 209, 224, 98, 123)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 81, 65, 223, 57, 101, 2, 238)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_linter_unnecessaryRwa;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`rw` already closes the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Use `rw` instead of `rwa`:"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(244, 42, 145, 170, 145, 147, 228, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rwa"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 15, 10, 164, 56, 218, 17, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Type mismatch: The rewritten hypothesis"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 113, 102, 14, 152, 233, 20, 47)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalRwa___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRwa___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalRwa___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRwa___lam__1___boxed, .m_arity = 14, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value)} };
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__5_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRwa___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRwa___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__11_value),LEAN_SCALAR_PTR_LITERAL(50, 16, 185, 246, 153, 187, 181, 153)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalRwa"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 139, 161, 211, 132, 56, 217, 52)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRwaAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rwaAt"};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 18, 214, 65, 184, 96, 194, 7)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwaAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwaAt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwaAt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwaAt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__5_value),LEAN_SCALAR_PTR_LITERAL(229, 146, 67, 234, 45, 36, 143, 176)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__6_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalRwaAt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalRwaAt___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwaAt___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalRwaAt"};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 65, 91, 100, 130, 171, 66, 201)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_();
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(lean_object* v_opts_61_, lean_object* v_opt_62_){
_start:
{
lean_object* v_name_63_; lean_object* v_defValue_64_; lean_object* v_map_65_; lean_object* v___x_66_; 
v_name_63_ = lean_ctor_get(v_opt_62_, 0);
v_defValue_64_ = lean_ctor_get(v_opt_62_, 1);
v_map_65_ = lean_ctor_get(v_opts_61_, 0);
v___x_66_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_65_, v_name_63_);
if (lean_obj_tag(v___x_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = lean_unbox(v_defValue_64_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; 
v_val_68_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v___x_66_, 1);
if (lean_obj_tag(v_val_68_) == 1)
{
uint8_t v_v_69_; 
v_v_69_ = lean_ctor_get_uint8(v_val_68_, 0);
lean_dec_ref_known(v_val_68_, 0);
return v_v_69_;
}
else
{
uint8_t v___x_70_; 
lean_dec(v_val_68_);
v___x_70_ = lean_unbox(v_defValue_64_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_71_, lean_object* v_opt_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v_opts_71_, v_opt_72_);
lean_dec_ref(v_opt_72_);
lean_dec_ref(v_opts_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(lean_object* v_msgData_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; lean_object* v_env_82_; uint8_t v___x_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v_toCold_86_; lean_object* v_mctx_87_; lean_object* v_lctx_88_; lean_object* v_options_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_env_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_env_82_);
lean_dec(v___x_81_);
v___x_83_ = 0;
v_env_84_ = l_Lean_Environment_setRecordingDeps(v_env_82_, v___x_83_);
v___x_85_ = lean_st_ref_get(v___y_77_);
v_toCold_86_ = lean_ctor_get(v___y_78_, 0);
v_mctx_87_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_mctx_87_);
lean_dec(v___x_85_);
v_lctx_88_ = lean_ctor_get(v___y_76_, 2);
v_options_89_ = lean_ctor_get(v_toCold_86_, 2);
lean_inc_ref(v_options_89_);
lean_inc_ref(v_lctx_88_);
v___x_90_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_90_, 0, v_env_84_);
lean_ctor_set(v___x_90_, 1, v_mctx_87_);
lean_ctor_set(v___x_90_, 2, v_lctx_88_);
lean_ctor_set(v___x_90_, 3, v_options_89_);
v___x_91_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_msgData_75_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msgData_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 1)
{
lean_object* v_pre_108_; 
v_pre_108_ = lean_ctor_get(v_x_107_, 0);
switch(lean_obj_tag(v_pre_108_))
{
case 1:
{
lean_object* v_pre_109_; 
v_pre_109_ = lean_ctor_get(v_pre_108_, 0);
switch(lean_obj_tag(v_pre_109_))
{
case 0:
{
lean_object* v_str_110_; lean_object* v_str_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_str_110_ = lean_ctor_get(v_x_107_, 1);
v_str_111_ = lean_ctor_get(v_pre_108_, 1);
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_113_ = lean_string_dec_eq(v_str_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_115_ = lean_string_dec_eq(v_str_111_, v___x_114_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_117_ = lean_string_dec_eq(v_str_110_, v___x_116_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
else
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_119_ = lean_string_dec_eq(v_str_110_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
case 1:
{
lean_object* v_pre_120_; 
v_pre_120_ = lean_ctor_get(v_pre_109_, 0);
if (lean_obj_tag(v_pre_120_) == 0)
{
lean_object* v_str_121_; lean_object* v_str_122_; lean_object* v_str_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_str_121_ = lean_ctor_get(v_x_107_, 1);
v_str_122_ = lean_ctor_get(v_pre_108_, 1);
v_str_123_ = lean_ctor_get(v_pre_109_, 1);
v___x_124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_125_ = lean_string_dec_eq(v_str_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_127_ = lean_string_dec_eq(v_str_122_, v___x_126_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_129_ = lean_string_dec_eq(v_str_121_, v___x_128_);
if (v___x_129_ == 0)
{
return v___x_129_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
default: 
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
case 0:
{
lean_object* v_str_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_str_132_ = lean_ctor_get(v_x_107_, 1);
v___x_133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_134_ = lean_string_dec_eq(v_str_132_, v___x_133_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
return v_suppressElabErrors_106_;
}
}
default: 
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_suppressElabErrors_boxed_139_; uint8_t v_res_140_; lean_object* v_r_141_; 
v_suppressElabErrors_boxed_139_ = lean_unbox(v_suppressElabErrors_137_);
v_res_140_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_139_, v_x_138_);
lean_dec(v_x_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_143_, lean_object* v_msgData_144_, uint8_t v_severity_145_, uint8_t v_isSilent_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v___y_153_; lean_object* v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v_toCold_160_; lean_object* v___y_161_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; uint8_t v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_217_; uint8_t v___y_218_; lean_object* v___y_219_; uint8_t v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___y_227_; uint8_t v___y_228_; uint8_t v___x_238_; uint8_t v___y_240_; uint8_t v___x_246_; 
v___x_238_ = 2;
v___x_246_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_238_);
if (v___x_246_ == 0)
{
v___y_240_ = v___x_246_;
goto v___jp_239_;
}
else
{
uint8_t v___x_247_; 
lean_inc_ref(v_msgData_144_);
v___x_247_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_144_);
if (v___x_247_ == 0)
{
v___y_240_ = v___x_247_;
goto v___jp_239_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v_msgData_144_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
v___jp_152_:
{
lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_env_168_; lean_object* v_nextMacroScope_169_; lean_object* v_ngen_170_; lean_object* v_auxDeclNGen_171_; lean_object* v_traceState_172_; lean_object* v_cache_173_; lean_object* v_recordedDeps_174_; lean_object* v_messages_175_; lean_object* v_infoState_176_; lean_object* v_snapshotTasks_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_188_; 
v_currNamespace_162_ = lean_ctor_get(v_toCold_160_, 4);
v_openDecls_163_ = lean_ctor_get(v_toCold_160_, 5);
lean_inc(v_openDecls_163_);
lean_inc(v_currNamespace_162_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_currNamespace_162_);
lean_ctor_set(v___x_164_, 1, v_openDecls_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___y_156_);
lean_inc_ref(v___y_154_);
lean_inc_ref(v___y_157_);
v___x_166_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_166_, 0, v___y_157_);
lean_ctor_set(v___x_166_, 1, v___y_159_);
lean_ctor_set(v___x_166_, 2, v___y_158_);
lean_ctor_set(v___x_166_, 3, v___y_154_);
lean_ctor_set(v___x_166_, 4, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5, v___y_155_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 1, v___y_153_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 2, v_isSilent_146_);
v___x_167_ = lean_st_ref_take(v___y_161_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
v_nextMacroScope_169_ = lean_ctor_get(v___x_167_, 1);
v_ngen_170_ = lean_ctor_get(v___x_167_, 2);
v_auxDeclNGen_171_ = lean_ctor_get(v___x_167_, 3);
v_traceState_172_ = lean_ctor_get(v___x_167_, 4);
v_cache_173_ = lean_ctor_get(v___x_167_, 5);
v_recordedDeps_174_ = lean_ctor_get(v___x_167_, 6);
v_messages_175_ = lean_ctor_get(v___x_167_, 7);
v_infoState_176_ = lean_ctor_get(v___x_167_, 8);
v_snapshotTasks_177_ = lean_ctor_get(v___x_167_, 9);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_188_ == 0)
{
v___x_179_ = v___x_167_;
v_isShared_180_ = v_isSharedCheck_188_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_snapshotTasks_177_);
lean_inc(v_infoState_176_);
lean_inc(v_messages_175_);
lean_inc(v_recordedDeps_174_);
lean_inc(v_cache_173_);
lean_inc(v_traceState_172_);
lean_inc(v_auxDeclNGen_171_);
lean_inc(v_ngen_170_);
lean_inc(v_nextMacroScope_169_);
lean_inc(v_env_168_);
lean_dec(v___x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_188_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_MessageLog_add(v___x_166_, v_messages_175_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 7, v___x_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_env_168_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_nextMacroScope_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_ngen_170_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_auxDeclNGen_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_traceState_172_);
lean_ctor_set(v_reuseFailAlloc_187_, 5, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_187_, 6, v_recordedDeps_174_);
lean_ctor_set(v_reuseFailAlloc_187_, 7, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_187_, 8, v_infoState_176_);
lean_ctor_set(v_reuseFailAlloc_187_, 9, v_snapshotTasks_177_);
v___x_184_ = v_reuseFailAlloc_187_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_st_ref_put(v___y_161_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_181_);
return v___x_186_;
}
}
}
v___jp_189_:
{
lean_object* v_fileName_198_; lean_object* v_fileMap_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_215_; 
v_fileName_198_ = lean_ctor_get(v___y_196_, 0);
v_fileMap_199_ = lean_ctor_get(v___y_196_, 1);
v___x_200_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_144_);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v___x_200_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_215_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref_n(v_fileMap_199_, 2);
v___x_206_ = l_Lean_FileMap_toPosition(v_fileMap_199_, v___y_193_);
lean_dec(v___y_193_);
v___x_207_ = l_Lean_FileMap_toPosition(v_fileMap_199_, v___y_197_);
lean_dec(v___y_197_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_195_ == 0)
{
lean_del_object(v___x_204_);
lean_dec_ref(v___y_190_);
v___y_153_ = v___y_192_;
v___y_154_ = v___x_209_;
v___y_155_ = v___y_194_;
v___y_156_ = v_a_202_;
v___y_157_ = v_fileName_198_;
v___y_158_ = v___x_208_;
v___y_159_ = v___x_206_;
v_toCold_160_ = v___y_191_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
else
{
uint8_t v___x_210_; 
lean_inc(v_a_202_);
v___x_210_ = l_Lean_MessageData_hasTag(v___y_190_, v_a_202_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref_known(v___x_208_, 1);
lean_dec_ref(v___x_206_);
lean_dec(v_a_202_);
v___x_211_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_213_ = v___x_204_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_del_object(v___x_204_);
v___y_153_ = v___y_192_;
v___y_154_ = v___x_209_;
v___y_155_ = v___y_194_;
v___y_156_ = v_a_202_;
v___y_157_ = v_fileName_198_;
v___y_158_ = v___x_208_;
v___y_159_ = v___x_206_;
v_toCold_160_ = v___y_191_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
}
}
}
v___jp_216_:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Syntax_getTailPos_x3f(v___y_222_, v___y_221_);
lean_dec(v___y_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_inc(v___y_223_);
v___y_190_ = v___y_217_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_223_;
v___y_194_ = v___y_221_;
v___y_195_ = v___y_218_;
v___y_196_ = v___y_219_;
v___y_197_ = v___y_223_;
goto v___jp_189_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___y_190_ = v___y_217_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_223_;
v___y_194_ = v___y_221_;
v___y_195_ = v___y_218_;
v___y_196_ = v___y_219_;
v___y_197_ = v_val_225_;
goto v___jp_189_;
}
}
v___jp_226_:
{
lean_object* v_toCold_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v_ref_234_; lean_object* v___x_235_; 
v_toCold_229_ = lean_ctor_get(v___y_149_, 0);
v_ref_230_ = lean_ctor_get(v___y_149_, 2);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v___y_149_, sizeof(void*)*3 + 2);
v___x_232_ = lean_box(v_suppressElabErrors_231_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_233_, 0, v___x_232_);
v_ref_234_ = l_Lean_replaceRef(v_ref_143_, v_ref_230_);
v___x_235_ = l_Lean_Syntax_getPos_x3f(v_ref_234_, v___y_227_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___f_233_;
v___y_218_ = v_suppressElabErrors_231_;
v___y_219_ = v_toCold_229_;
v___y_220_ = v___y_228_;
v___y_221_ = v___y_227_;
v___y_222_ = v_ref_234_;
v___y_223_ = v___x_236_;
goto v___jp_216_;
}
else
{
lean_object* v_val_237_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_235_, 1);
v___y_217_ = v___f_233_;
v___y_218_ = v_suppressElabErrors_231_;
v___y_219_ = v_toCold_229_;
v___y_220_ = v___y_228_;
v___y_221_ = v___y_227_;
v___y_222_ = v_ref_234_;
v___y_223_ = v_val_237_;
goto v___jp_216_;
}
}
v___jp_239_:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 1;
v___x_242_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_241_);
if (v___x_242_ == 0)
{
v___y_227_ = v___y_240_;
v___y_228_ = v_severity_145_;
goto v___jp_226_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_149_);
v___x_244_ = l_Lean_warningAsError;
v___x_245_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v___x_243_, v___x_244_);
lean_dec_ref(v___x_243_);
if (v___x_245_ == 0)
{
v___y_227_ = v___y_240_;
v___y_228_ = v_severity_145_;
goto v___jp_226_;
}
else
{
v___y_227_ = v___y_240_;
v___y_228_ = v___x_238_;
goto v___jp_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_250_, lean_object* v_msgData_251_, lean_object* v_severity_252_, lean_object* v_isSilent_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
uint8_t v_severity_boxed_259_; uint8_t v_isSilent_boxed_260_; lean_object* v_res_261_; 
v_severity_boxed_259_ = lean_unbox(v_severity_252_);
v_isSilent_boxed_260_ = lean_unbox(v_isSilent_253_);
v_res_261_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_250_, v_msgData_251_, v_severity_boxed_259_, v_isSilent_boxed_260_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v_ref_250_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object* v_ref_262_, lean_object* v_msgData_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = 1;
v___x_274_ = 0;
v___x_275_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_262_, v_msgData_263_, v___x_273_, v___x_274_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object* v_ref_276_, lean_object* v_msgData_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_ref_276_, v_msgData_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_ref_276_);
return v_res_287_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object* v_linterOption_294_, lean_object* v_stx_295_, lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_name_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_324_; 
v_name_306_ = lean_ctor_get(v_linterOption_294_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_linterOption_294_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v_linterOption_294_, 1);
lean_dec(v_unused_325_);
v___x_308_ = v_linterOption_294_;
v_isShared_309_ = v_isSharedCheck_324_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_name_306_);
lean_dec(v_linterOption_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_324_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1);
lean_inc(v_name_306_);
v___x_311_ = l_Lean_MessageData_ofName(v_name_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 7);
lean_ctor_set(v___x_308_, 1, v___x_311_);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_323_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_disable_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_314_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v_disable_316_ = l_Lean_MessageData_note(v___x_315_);
v___x_317_ = l_Lean_Linter_linterMessageTag;
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v_msg_296_);
lean_ctor_set(v___x_318_, 1, v_disable_316_);
v___x_319_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_320_, 0, v_name_306_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_inc(v_stx_295_);
v___x_321_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_321_, 0, v_stx_295_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_stx_295_, v___x_321_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v_stx_295_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object* v_linterOption_326_, lean_object* v_stx_327_, lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v_linterOption_326_, v_stx_327_, v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object* v_o_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_toEnvExtension_346_; lean_object* v_asyncMode_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v_merged_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v___x_342_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_343_ = lean_st_ref_get(v___y_340_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_346_ = lean_ctor_get(v___x_345_, 0);
v_asyncMode_347_ = lean_ctor_get(v_toEnvExtension_346_, 2);
v___x_348_ = lean_box(0);
v___x_349_ = 0;
v___x_350_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_342_, v___x_345_, v_env_344_, v_asyncMode_347_, v___x_348_, v___x_349_);
v_merged_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v___x_350_, 1);
lean_dec(v_unused_360_);
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_merged_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_merged_351_);
lean_ctor_set(v___x_353_, 0, v_o_339_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_o_339_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_merged_351_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg___boxed(lean_object* v_o_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_361_, v___y_362_);
lean_dec(v___y_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_371_);
v___x_375_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v___x_374_, v___y_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0___boxed(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5));
v___x_396_ = l_Lean_MessageData_ofFormat(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(lean_object* v_initialState_397_, lean_object* v_ref_398_, lean_object* v_replacement_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_457_; 
v___x_409_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_457_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_457_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_457_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = l_Lean_Elab_Tactic_linter_unnecessaryRwa;
v___x_415_ = l_Lean_Linter_getLinterValue(v___x_414_, v_a_410_);
lean_dec(v_a_410_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec(v_replacement_399_);
lean_dec(v_ref_398_);
lean_dec_ref(v_initialState_397_);
v___x_416_ = lean_box(0);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_416_);
v___x_418_ = v___x_412_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_del_object(v___x_412_);
v___x_420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1);
v___x_421_ = lean_box(0);
lean_inc(v_replacement_399_);
v___x_422_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_397_, v_replacement_399_, v___x_421_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; uint8_t v___x_424_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = lean_unbox(v_a_423_);
lean_dec(v_a_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec(v_replacement_399_);
v___x_425_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_414_, v_ref_398_, v___x_420_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3));
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_replacement_399_);
v___x_428_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_421_);
lean_ctor_set(v___x_428_, 2, v___x_421_);
lean_ctor_set(v___x_428_, 3, v___x_421_);
lean_ctor_set(v___x_428_, 4, v___x_421_);
lean_ctor_set(v___x_428_, 5, v___x_421_);
lean_inc(v_ref_398_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_ref_398_);
v___x_430_ = 4;
lean_inc_ref(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_431_, 0, v___x_428_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_421_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3, v___x_430_);
v___x_432_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_array_push(v___x_434_, v___x_431_);
v___x_436_ = 0;
v___x_437_ = l_Lean_MessageData_hint(v___x_432_, v___x_435_, v___x_429_, v___x_421_, v___x_436_, v_a_406_, v_a_407_);
lean_dec_ref(v___x_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_420_);
lean_ctor_set(v___x_439_, 1, v_a_438_);
v___x_440_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_414_, v_ref_398_, v___x_439_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_440_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_ref_398_);
v_a_441_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_437_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_replacement_399_);
lean_dec(v_ref_398_);
v_a_449_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_422_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_422_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___boxed(lean_object* v_initialState_458_, lean_object* v_ref_459_, lean_object* v_replacement_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_initialState_458_, v_ref_459_, v_replacement_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(lean_object* v_o_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_471_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___boxed(lean_object* v_o_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(v_o_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(lean_object* v_ref_493_, lean_object* v_msgData_494_, uint8_t v_severity_495_, uint8_t v_isSilent_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_493_, v_msgData_494_, v_severity_495_, v_isSilent_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_507_, lean_object* v_msgData_508_, lean_object* v_severity_509_, lean_object* v_isSilent_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_severity_boxed_520_; uint8_t v_isSilent_boxed_521_; lean_object* v_res_522_; 
v_severity_boxed_520_ = lean_unbox(v_severity_509_);
v_isSilent_boxed_521_ = lean_unbox(v_isSilent_510_);
v_res_522_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(v_ref_507_, v_msgData_508_, v_severity_boxed_520_, v_isSilent_boxed_521_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v_ref_507_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_ref_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_ref_562_ = lean_ctor_get(v___y_559_, 2);
v___x_563_ = 0;
v___x_564_ = l_Lean_SourceInfo_fromRef(v_ref_562_, v___x_563_);
v___x_565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
lean_inc_n(v___x_564_, 6);
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_564_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_564_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_Syntax_node1(v___x_564_, v___x_571_, v___x_573_);
v___x_575_ = l_Lean_Syntax_node1(v___x_564_, v___x_570_, v___x_574_);
v___x_576_ = l_Lean_Syntax_node1(v___x_564_, v___x_569_, v___x_575_);
v___x_577_ = l_Lean_Syntax_node1(v___x_564_, v___x_568_, v___x_576_);
v___x_578_ = l_Lean_Syntax_node2(v___x_564_, v___x_565_, v___x_567_, v___x_577_);
v___x_579_ = l_Lean_Elab_Tactic_evalTactic(v___x_578_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_589_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = 1;
v___x_584_ = lean_box(v___x_583_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_579_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed(lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(lean_object* v___f_608_, lean_object* v_close_609_, lean_object* v_a_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_612_, v___y_614_, v___y_616_, v___y_618_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_608_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_dec(v_a_621_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_close_609_);
return v___x_622_;
}
else
{
lean_object* v_a_623_; uint8_t v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v___x_624_ = l_Lean_Exception_isInterrupt(v_a_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
lean_inc(v_a_623_);
v___x_625_ = l_Lean_Exception_isRuntime(v_a_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref_known(v___x_622_, 1);
v___x_626_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_621_, v___x_625_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; 
lean_dec_ref_known(v___x_626_, 1);
v___x_627_ = lean_apply_10(v_close_609_, v_a_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, lean_box(0));
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v___x_627_, 0);
lean_dec(v_unused_636_);
v___x_629_ = v___x_627_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_dec(v___x_627_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_box(v___x_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_a_637_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_627_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_627_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_close_609_);
v_a_645_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_626_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_626_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_dec(v_a_621_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_close_609_);
return v___x_622_;
}
}
else
{
lean_dec(v_a_621_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_close_609_);
return v___x_622_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_close_609_);
lean_dec_ref(v___f_608_);
v_a_653_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_620_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_620_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed(lean_object* v___f_661_, lean_object* v_close_662_, lean_object* v_a_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(v___f_661_, v_close_662_, v_a_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(lean_object* v_rewrite_711_, lean_object* v___f_712_, lean_object* v_close_713_, lean_object* v_ref_714_, lean_object* v_replacement_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_717_, v___y_719_, v___y_721_, v___y_723_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
v___x_790_ = lean_apply_9(v_rewrite_711_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___f_792_; lean_object* v___x_793_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___f_792_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_792_, 0, v___f_712_);
lean_closure_set(v___f_792_, 1, v_close_713_);
lean_closure_set(v___f_792_, 2, v_a_791_);
v___x_793_ = l_Lean_Elab_Tactic_focus___redArg(v___f_792_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_795_) == 0)
{
uint8_t v___x_796_; 
v___x_796_ = lean_unbox(v_a_794_);
lean_dec(v_a_794_);
if (v___x_796_ == 0)
{
lean_dec_ref_known(v___x_795_, 1);
lean_dec(v_a_789_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
goto v___jp_725_;
}
else
{
lean_object* v_a_797_; uint8_t v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_795_, 1);
v___x_798_ = l_List_isEmpty___redArg(v_a_797_);
lean_dec(v_a_797_);
if (v___x_798_ == 0)
{
lean_dec(v_a_789_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
goto v___jp_725_;
}
else
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_a_789_, v_ref_714_, v_replacement_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_dec_ref_known(v___x_799_, 1);
goto v___jp_725_;
}
else
{
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_a_794_);
lean_dec(v_a_789_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
v_a_800_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_795_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_789_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
v_a_808_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_793_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_793_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_789_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
lean_dec_ref(v_close_713_);
lean_dec_ref(v___f_712_);
v_a_816_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_790_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_790_);
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
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_replacement_715_);
lean_dec(v_ref_714_);
lean_dec_ref(v_close_713_);
lean_dec_ref(v___f_712_);
lean_dec_ref(v_rewrite_711_);
v_a_824_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_788_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_788_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
v___jp_725_:
{
lean_object* v_ref_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_ref_726_ = lean_ctor_get(v___y_722_, 2);
v___x_727_ = 0;
v___x_728_ = l_Lean_SourceInfo_fromRef(v_ref_726_, v___x_727_);
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1));
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2));
lean_inc_n(v___x_728_, 37);
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_728_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4));
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_728_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6));
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_728_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
v___x_741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9));
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_728_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_728_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_728_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_Syntax_node1(v___x_728_, v___x_747_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node2(v___x_728_, v___x_744_, v___x_746_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_756_);
lean_inc_ref_n(v___x_743_, 2);
v___x_758_ = l_Lean_Syntax_node2(v___x_728_, v___x_741_, v___x_743_, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_728_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
v___x_762_ = l_Lean_Syntax_node1(v___x_728_, v___x_760_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node2(v___x_728_, v___x_741_, v___x_743_, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13));
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_728_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
v___x_770_ = l_Lean_Syntax_node1(v___x_728_, v___x_768_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___x_728_, v___x_741_, v___x_743_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node3(v___x_728_, v___x_734_, v___x_758_, v___x_766_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node2(v___x_728_, v___x_739_, v___x_740_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_778_);
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_728_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Syntax_node3(v___x_728_, v___x_735_, v___x_737_, v___x_779_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node1(v___x_728_, v___x_734_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___x_728_, v___x_733_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_728_, v___x_732_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node2(v___x_728_, v___x_729_, v___x_731_, v___x_785_);
v___x_787_ = l_Lean_Elab_Tactic_evalTactic(v___x_786_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object* v_rewrite_832_, lean_object* v___f_833_, lean_object* v_close_834_, lean_object* v_ref_835_, lean_object* v_replacement_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(v_rewrite_832_, v___f_833_, v_close_834_, v_ref_835_, v_replacement_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object* v_ref_848_, lean_object* v_rewrite_849_, lean_object* v_replacement_850_, lean_object* v_close_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; 
v___f_861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0));
v___f_862_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed), 14, 5);
lean_closure_set(v___f_862_, 0, v_rewrite_849_);
lean_closure_set(v___f_862_, 1, v___f_861_);
lean_closure_set(v___f_862_, 2, v_close_851_);
lean_closure_set(v___f_862_, 3, v_ref_848_);
lean_closure_set(v___f_862_, 4, v_replacement_850_);
v___x_863_ = l_Lean_Elab_Tactic_focus___redArg(v___f_862_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object* v_ref_864_, lean_object* v_rewrite_865_, lean_object* v_replacement_866_, lean_object* v_close_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_864_, v_rewrite_865_, v_replacement_866_, v_close_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object* v_00_u03b1_878_, lean_object* v_ref_879_, lean_object* v_rewrite_880_, lean_object* v_replacement_881_, lean_object* v_close_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_879_, v_rewrite_880_, v_replacement_881_, v_close_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object* v_00_u03b1_893_, lean_object* v_ref_894_, lean_object* v_rewrite_895_, lean_object* v_replacement_896_, lean_object* v_close_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(v_00_u03b1_893_, v_ref_894_, v_rewrite_895_, v_replacement_896_, v_close_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_ref_914_; lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_ref_914_ = lean_ctor_get(v___y_911_, 2);
v___x_915_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_inc(v_ref_914_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_ref_914_);
lean_ctor_set(v___x_920_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object* v_msg_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object* v_fvarId_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_945_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___x_967_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = l_Lean_mkFVar(v_fvarId_943_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc_ref(v___x_955_);
v___x_967_ = lean_infer_type(v___x_955_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_MVarId_getType(v_a_954_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; uint8_t v_foApprox_972_; uint8_t v_ctxApprox_973_; uint8_t v_quasiPatternApprox_974_; uint8_t v_constApprox_975_; uint8_t v_isDefEqStuckEx_976_; uint8_t v_unificationHints_977_; uint8_t v_proofIrrelevance_978_; uint8_t v_offsetCnstrs_979_; uint8_t v_transparency_980_; uint8_t v_etaStruct_981_; uint8_t v_univApprox_982_; uint8_t v_iota_983_; uint8_t v_beta_984_; uint8_t v_proj_985_; uint8_t v_zeta_986_; uint8_t v_zetaDelta_987_; uint8_t v_zetaUnused_988_; uint8_t v_zetaHave_989_; uint8_t v_canUnfoldPredicateConfig_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1041_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Meta_Context_config(v___y_948_);
v_foApprox_972_ = lean_ctor_get_uint8(v___x_971_, 0);
v_ctxApprox_973_ = lean_ctor_get_uint8(v___x_971_, 1);
v_quasiPatternApprox_974_ = lean_ctor_get_uint8(v___x_971_, 2);
v_constApprox_975_ = lean_ctor_get_uint8(v___x_971_, 3);
v_isDefEqStuckEx_976_ = lean_ctor_get_uint8(v___x_971_, 4);
v_unificationHints_977_ = lean_ctor_get_uint8(v___x_971_, 5);
v_proofIrrelevance_978_ = lean_ctor_get_uint8(v___x_971_, 6);
v_offsetCnstrs_979_ = lean_ctor_get_uint8(v___x_971_, 8);
v_transparency_980_ = lean_ctor_get_uint8(v___x_971_, 9);
v_etaStruct_981_ = lean_ctor_get_uint8(v___x_971_, 10);
v_univApprox_982_ = lean_ctor_get_uint8(v___x_971_, 11);
v_iota_983_ = lean_ctor_get_uint8(v___x_971_, 12);
v_beta_984_ = lean_ctor_get_uint8(v___x_971_, 13);
v_proj_985_ = lean_ctor_get_uint8(v___x_971_, 14);
v_zeta_986_ = lean_ctor_get_uint8(v___x_971_, 15);
v_zetaDelta_987_ = lean_ctor_get_uint8(v___x_971_, 16);
v_zetaUnused_988_ = lean_ctor_get_uint8(v___x_971_, 17);
v_zetaHave_989_ = lean_ctor_get_uint8(v___x_971_, 18);
v_canUnfoldPredicateConfig_990_ = lean_ctor_get_uint8(v___x_971_, 19);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_992_ = v___x_971_;
v_isShared_993_ = v_isSharedCheck_1041_;
goto v_resetjp_991_;
}
else
{
lean_dec(v___x_971_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1041_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v_trackZetaDelta_994_; lean_object* v_zetaDeltaSet_995_; lean_object* v_lctx_996_; lean_object* v_localInstances_997_; lean_object* v_defEqCtx_x3f_998_; lean_object* v_synthPendingDepth_999_; lean_object* v_customCanUnfoldPredicate_x3f_1000_; uint8_t v_univApprox_1001_; uint8_t v_inTypeClassResolution_1002_; uint8_t v_cacheInferType_1003_; uint8_t v___x_1004_; lean_object* v___x_1006_; 
v_trackZetaDelta_994_ = lean_ctor_get_uint8(v___y_948_, sizeof(void*)*7);
v_zetaDeltaSet_995_ = lean_ctor_get(v___y_948_, 1);
v_lctx_996_ = lean_ctor_get(v___y_948_, 2);
v_localInstances_997_ = lean_ctor_get(v___y_948_, 3);
v_defEqCtx_x3f_998_ = lean_ctor_get(v___y_948_, 4);
v_synthPendingDepth_999_ = lean_ctor_get(v___y_948_, 5);
v_customCanUnfoldPredicate_x3f_1000_ = lean_ctor_get(v___y_948_, 6);
v_univApprox_1001_ = lean_ctor_get_uint8(v___y_948_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1002_ = lean_ctor_get_uint8(v___y_948_, sizeof(void*)*7 + 2);
v_cacheInferType_1003_ = lean_ctor_get_uint8(v___y_948_, sizeof(void*)*7 + 3);
v___x_1004_ = 1;
if (v_isShared_993_ == 0)
{
v___x_1006_ = v___x_992_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 0, v_foApprox_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 1, v_ctxApprox_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 2, v_quasiPatternApprox_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 3, v_constApprox_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 4, v_isDefEqStuckEx_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 5, v_unificationHints_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 6, v_proofIrrelevance_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 8, v_offsetCnstrs_979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 9, v_transparency_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 10, v_etaStruct_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 11, v_univApprox_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 12, v_iota_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 13, v_beta_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 14, v_proj_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 15, v_zeta_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 16, v_zetaDelta_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 17, v_zetaUnused_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 18, v_zetaHave_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, 19, v_canUnfoldPredicateConfig_990_);
v___x_1006_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
uint64_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_ctor_set_uint8(v___x_1006_, 7, v___x_1004_);
v___x_1007_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set_uint64(v___x_1008_, sizeof(void*)*1, v___x_1007_);
lean_inc(v_customCanUnfoldPredicate_x3f_1000_);
lean_inc(v_synthPendingDepth_999_);
lean_inc(v_defEqCtx_x3f_998_);
lean_inc_ref(v_localInstances_997_);
lean_inc_ref(v_lctx_996_);
lean_inc(v_zetaDeltaSet_995_);
v___x_1009_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_zetaDeltaSet_995_);
lean_ctor_set(v___x_1009_, 2, v_lctx_996_);
lean_ctor_set(v___x_1009_, 3, v_localInstances_997_);
lean_ctor_set(v___x_1009_, 4, v_defEqCtx_x3f_998_);
lean_ctor_set(v___x_1009_, 5, v_synthPendingDepth_999_);
lean_ctor_set(v___x_1009_, 6, v_customCanUnfoldPredicate_x3f_1000_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*7, v_trackZetaDelta_994_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*7 + 1, v_univApprox_1001_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1002_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*7 + 3, v_cacheInferType_1003_);
lean_inc(v_a_970_);
lean_inc(v_a_968_);
v___x_1010_ = l_Lean_Meta_isExprDefEq(v_a_968_, v_a_970_, v___x_1009_, v___y_949_, v___y_950_, v___y_951_);
lean_dec_ref_known(v___x_1009_, 7);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = lean_unbox(v_a_1011_);
lean_dec(v_a_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2));
v___x_1015_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_968_, v_a_970_, v___x_1013_, v___x_1014_, v___y_948_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4);
v___x_1018_ = l_Lean_indentExpr(v___x_955_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_a_1016_);
v___x_1023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v___x_1022_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v___x_1023_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v___x_955_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
v_a_1024_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1015_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_dec(v_a_970_);
lean_dec(v_a_968_);
v___y_957_ = v___y_945_;
v___y_958_ = v___y_946_;
v___y_959_ = v___y_947_;
v___y_960_ = v___y_948_;
v___y_961_ = v___y_949_;
v___y_962_ = v___y_950_;
v___y_963_ = v___y_951_;
goto v___jp_956_;
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_970_);
lean_dec(v_a_968_);
lean_dec_ref(v___x_955_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
v_a_1032_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1010_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1010_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_968_);
lean_dec_ref(v___x_955_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
v_a_1042_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_969_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_969_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___x_955_);
lean_dec(v_a_954_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
v_a_1050_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_967_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_967_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
v___jp_956_:
{
lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1));
v___x_965_ = 1;
v___x_966_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_964_, v___x_955_, v___x_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v___x_966_;
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v_fvarId_943_);
v_a_1058_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_953_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_953_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object* v_fvarId_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(v_fvarId_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object* v_fvarId_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; 
v___f_1087_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1087_, 0, v_fvarId_1077_);
v___x_1088_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1087_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object* v_fvarId_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(v_fvarId_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object* v_00_u03b1_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_1101_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_msg_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(v_00_u03b1_1112_, v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg(){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object* v_00_u03b1_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object* v_00_u03b1_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(v_00_u03b1_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_ref_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_ref_1163_ = lean_ctor_get(v___y_1160_, 2);
v___x_1164_ = 0;
v___x_1165_ = l_Lean_SourceInfo_fromRef(v_ref_1163_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object* v___f_1177_, lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1186_);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
v___x_1191_ = lean_apply_9(v___f_1177_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, lean_box(0));
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_n(v_a_1192_, 2);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_1194_ = l_Lean_Name_mkStr4(v___x_1178_, v___x_1179_, v___x_1180_, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1192_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
v___x_1196_ = l_Lean_Syntax_node1(v_a_1192_, v___x_1194_, v___x_1195_);
v___x_1197_ = l_Lean_Elab_Tactic_evalTactic(v___x_1196_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1197_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v___x_1180_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v___x_1178_);
v_a_1198_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1191_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1191_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object* v___f_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Elab_Tactic_evalRwa___lam__1(v___f_1206_, v___x_1207_, v___x_1208_, v___x_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRwa___closed__10(void){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Array_mkArray0___redArg();
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object* v_stx_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
lean_inc(v_stx_1259_);
v___x_1270_ = l_Lean_Syntax_isOfKind(v_stx_1259_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec(v_stx_1259_);
v___x_1271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = l_Lean_Syntax_getArg(v_stx_1259_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1273_);
v___x_1275_ = l_Lean_Syntax_isOfKind(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v___x_1273_);
lean_dec(v_stx_1259_);
v___x_1276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1276_;
}
else
{
lean_object* v_ref_1277_; lean_object* v___f_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_ref_1277_ = lean_ctor_get(v_a_1266_, 2);
v___f_1278_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__4));
v___x_1279_ = 0;
v___x_1280_ = l_Lean_SourceInfo_fromRef(v_ref_1277_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__6));
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__7));
lean_inc_n(v___x_1280_, 3);
v___x_1283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1280_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1286_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1280_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
lean_ctor_set(v___x_1287_, 2, v___x_1286_);
lean_inc_ref(v___x_1287_);
v___x_1288_ = l_Lean_Syntax_node1(v___x_1280_, v___x_1284_, v___x_1287_);
lean_inc(v___x_1273_);
v___x_1289_ = l_Lean_Syntax_node4(v___x_1280_, v___x_1281_, v___x_1283_, v___x_1288_, v___x_1273_, v___x_1287_);
v___x_1290_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_n(v_a_1291_, 4);
lean_dec_ref(v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1295_, 0, v_a_1291_);
lean_ctor_set(v___x_1295_, 1, v___x_1285_);
lean_ctor_set(v___x_1295_, 2, v___x_1286_);
lean_inc_ref(v___x_1295_);
v___x_1296_ = l_Lean_Syntax_node1(v_a_1291_, v___x_1284_, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node4(v_a_1291_, v___x_1292_, v___x_1294_, v___x_1296_, v___x_1273_, v___x_1295_);
v___x_1298_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1298_, 0, v___x_1289_);
v___x_1299_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1259_, v___x_1298_, v___x_1297_, v___f_1278_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object* v_stx_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Elab_Tactic_evalRwa(v_stx_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1(){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1318_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1));
v___x_1321_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwa___boxed), 10, 0);
v___x_1322_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1318_, v___x_1319_, v___x_1320_, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t v___x_1325_, lean_object* v_fvarId_1326_, uint8_t v_symm_1327_, lean_object* v_term_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1338_ = 2;
v___x_1339_ = lean_box(0);
v___x_1340_ = 0;
v___x_1341_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1, v___x_1338_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1 + 1, v___x_1325_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1 + 2, v___x_1340_);
v___x_1342_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_term_1328_, v_symm_1327_, v_fvarId_1326_, v___x_1341_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object* v___x_1343_, lean_object* v_fvarId_1344_, lean_object* v_symm_1345_, lean_object* v_term_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_2496__boxed_1356_; uint8_t v_symm_boxed_1357_; lean_object* v_res_1358_; 
v___x_2496__boxed_1356_ = lean_unbox(v___x_1343_);
v_symm_boxed_1357_ = lean_unbox(v_symm_1345_);
v_res_1358_ = l_Lean_Elab_Tactic_evalRwaAt___lam__0(v___x_2496__boxed_1356_, v_fvarId_1344_, v_symm_boxed_1357_, v_term_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object* v___x_1359_, lean_object* v_stx_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___f_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Elab_Tactic_getFVarId(v___x_1359_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_Syntax_getArg(v_stx_1360_, v___x_1361_);
v___x_1376_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v___x_1375_, v___x_1362_, v_a_1374_, v___f_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1376_;
}
else
{
lean_dec_ref(v___f_1363_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object* v___x_1377_, lean_object* v_stx_1378_, lean_object* v___x_1379_, lean_object* v___x_1380_, lean_object* v___f_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Elab_Tactic_evalRwaAt___lam__1(v___x_1377_, v_stx_1378_, v___x_1379_, v___x_1380_, v___f_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
lean_dec(v_stx_1378_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object* v_stx_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
lean_inc(v_stx_1412_);
v___x_1423_ = l_Lean_Syntax_isOfKind(v_stx_1412_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec(v_stx_1412_);
v___x_1424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_1412_, v___x_1425_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1426_);
v___x_1428_ = l_Lean_Syntax_isOfKind(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v___x_1426_);
lean_dec(v_stx_1412_);
v___x_1429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1429_;
}
else
{
lean_object* v_ref_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_ref_1430_ = lean_ctor_get(v_a_1419_, 2);
v___x_1431_ = lean_box(v___x_1428_);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1432_, 0, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_unsigned_to_nat(3u);
v___x_1435_ = l_Lean_Syntax_getArg(v_stx_1412_, v___x_1434_);
lean_inc(v___x_1426_);
lean_inc(v_stx_1412_);
lean_inc(v___x_1435_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1436_, 0, v___x_1435_);
lean_closure_set(v___f_1436_, 1, v_stx_1412_);
lean_closure_set(v___f_1436_, 2, v___x_1433_);
lean_closure_set(v___f_1436_, 3, v___x_1426_);
lean_closure_set(v___f_1436_, 4, v___f_1432_);
v___x_1437_ = 0;
v___x_1438_ = l_Lean_SourceInfo_fromRef(v_ref_1430_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
lean_inc_n(v___x_1438_, 8);
v___x_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1438_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1438_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v___x_1444_);
v___x_1446_ = l_Lean_Syntax_node1(v___x_1438_, v___x_1442_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__3));
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__4));
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1438_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__6));
v___x_1451_ = l_Lean_Syntax_node1(v___x_1438_, v___x_1443_, v___x_1435_);
v___x_1452_ = l_Lean_Syntax_node1(v___x_1438_, v___x_1450_, v___x_1451_);
v___x_1453_ = l_Lean_Syntax_node2(v___x_1438_, v___x_1447_, v___x_1449_, v___x_1452_);
v___x_1454_ = l_Lean_Syntax_node1(v___x_1438_, v___x_1443_, v___x_1453_);
v___x_1455_ = l_Lean_Syntax_node4(v___x_1438_, v___x_1439_, v___x_1441_, v___x_1446_, v___x_1426_, v___x_1454_);
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__7));
v___x_1457_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1412_, v___f_1436_, v___x_1455_, v___x_1456_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object* v_stx_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Elab_Tactic_evalRwaAt(v_stx_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1(){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1));
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___boxed), 10, 0);
v___x_1480_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1476_, v___x_1477_, v___x_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
return v_res_1482_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rwa(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_linter_unnecessaryRwa = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_linter_unnecessaryRwa);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Rwa(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rwa(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Rwa(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Rwa(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Rwa(builtin);
}
#ifdef __cplusplus
}
#endif
