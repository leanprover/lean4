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
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_106_, uint8_t v___y_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 1)
{
lean_object* v_pre_109_; 
v_pre_109_ = lean_ctor_get(v_x_108_, 0);
switch(lean_obj_tag(v_pre_109_))
{
case 1:
{
lean_object* v_pre_110_; 
v_pre_110_ = lean_ctor_get(v_pre_109_, 0);
switch(lean_obj_tag(v_pre_110_))
{
case 0:
{
lean_object* v_str_111_; lean_object* v_str_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_str_111_ = lean_ctor_get(v_x_108_, 1);
v_str_112_ = lean_ctor_get(v_pre_109_, 1);
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_114_ = lean_string_dec_eq(v_str_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_116_ = lean_string_dec_eq(v_str_112_, v___x_115_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_118_ = lean_string_dec_eq(v_str_111_, v___x_117_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
else
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_120_ = lean_string_dec_eq(v_str_111_, v___x_119_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
case 1:
{
lean_object* v_pre_121_; 
v_pre_121_ = lean_ctor_get(v_pre_110_, 0);
if (lean_obj_tag(v_pre_121_) == 0)
{
lean_object* v_str_122_; lean_object* v_str_123_; lean_object* v_str_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_str_122_ = lean_ctor_get(v_x_108_, 1);
v_str_123_ = lean_ctor_get(v_pre_109_, 1);
v_str_124_ = lean_ctor_get(v_pre_110_, 1);
v___x_125_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_126_ = lean_string_dec_eq(v_str_124_, v___x_125_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_128_ = lean_string_dec_eq(v_str_123_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_130_ = lean_string_dec_eq(v_str_122_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
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
return v___y_107_;
}
}
default: 
{
return v___y_107_;
}
}
}
case 0:
{
lean_object* v_str_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_str_131_ = lean_ctor_get(v_x_108_, 1);
v___x_132_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_133_ = lean_string_dec_eq(v_str_131_, v___x_132_);
if (v___x_133_ == 0)
{
return v___x_133_;
}
else
{
return v_suppressElabErrors_106_;
}
}
default: 
{
return v___y_107_;
}
}
}
else
{
return v___y_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_134_, lean_object* v___y_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_suppressElabErrors_boxed_137_; uint8_t v___y_5684__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_suppressElabErrors_boxed_137_ = lean_unbox(v_suppressElabErrors_134_);
v___y_5684__boxed_138_ = lean_unbox(v___y_135_);
v_res_139_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_137_, v___y_5684__boxed_138_, v_x_136_);
lean_dec(v_x_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_142_, lean_object* v_msgData_143_, uint8_t v_severity_144_, uint8_t v_isSilent_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; uint8_t v___y_157_; lean_object* v___y_158_; lean_object* v_toCold_159_; lean_object* v___y_160_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; uint8_t v___y_195_; lean_object* v___y_196_; lean_object* v___y_216_; uint8_t v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; uint8_t v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; uint8_t v___y_226_; uint8_t v___y_227_; uint8_t v___y_228_; uint8_t v___x_239_; uint8_t v___y_241_; uint8_t v___y_242_; uint8_t v___y_243_; uint8_t v___y_245_; uint8_t v___x_253_; 
v___x_239_ = 2;
v___x_253_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_239_);
if (v___x_253_ == 0)
{
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
uint8_t v___x_254_; 
lean_inc_ref(v_msgData_143_);
v___x_254_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_143_);
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
v___jp_151_:
{
lean_object* v_currNamespace_161_; lean_object* v_openDecls_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v_nextMacroScope_168_; lean_object* v_ngen_169_; lean_object* v_auxDeclNGen_170_; lean_object* v_traceState_171_; lean_object* v_cache_172_; lean_object* v_recordedDeps_173_; lean_object* v_messages_174_; lean_object* v_infoState_175_; lean_object* v_snapshotTasks_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
v_currNamespace_161_ = lean_ctor_get(v_toCold_159_, 4);
v_openDecls_162_ = lean_ctor_get(v_toCold_159_, 5);
lean_inc(v_openDecls_162_);
lean_inc(v_currNamespace_161_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_currNamespace_161_);
lean_ctor_set(v___x_163_, 1, v_openDecls_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___y_158_);
lean_inc_ref(v___y_156_);
lean_inc_ref(v___y_152_);
v___x_165_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_165_, 0, v___y_152_);
lean_ctor_set(v___x_165_, 1, v___y_154_);
lean_ctor_set(v___x_165_, 2, v___y_153_);
lean_ctor_set(v___x_165_, 3, v___y_156_);
lean_ctor_set(v___x_165_, 4, v___x_164_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5, v___y_157_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 1, v___y_155_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 2, v_isSilent_145_);
v___x_166_ = lean_st_ref_take(v___y_160_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
v_nextMacroScope_168_ = lean_ctor_get(v___x_166_, 1);
v_ngen_169_ = lean_ctor_get(v___x_166_, 2);
v_auxDeclNGen_170_ = lean_ctor_get(v___x_166_, 3);
v_traceState_171_ = lean_ctor_get(v___x_166_, 4);
v_cache_172_ = lean_ctor_get(v___x_166_, 5);
v_recordedDeps_173_ = lean_ctor_get(v___x_166_, 6);
v_messages_174_ = lean_ctor_get(v___x_166_, 7);
v_infoState_175_ = lean_ctor_get(v___x_166_, 8);
v_snapshotTasks_176_ = lean_ctor_get(v___x_166_, 9);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_187_ == 0)
{
v___x_178_ = v___x_166_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snapshotTasks_176_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_174_);
lean_inc(v_recordedDeps_173_);
lean_inc(v_cache_172_);
lean_inc(v_traceState_171_);
lean_inc(v_auxDeclNGen_170_);
lean_inc(v_ngen_169_);
lean_inc(v_nextMacroScope_168_);
lean_inc(v_env_167_);
lean_dec(v___x_166_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_180_ = lean_box(0);
v___x_181_ = l_Lean_MessageLog_add(v___x_165_, v_messages_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 7, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_env_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_nextMacroScope_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_ngen_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_auxDeclNGen_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_traceState_171_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_cache_172_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v_recordedDeps_173_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v_infoState_175_);
lean_ctor_set(v_reuseFailAlloc_186_, 9, v_snapshotTasks_176_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_st_ref_put(v___y_160_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
return v___x_185_;
}
}
}
v___jp_188_:
{
lean_object* v_fileName_197_; lean_object* v_fileMap_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v_fileName_197_ = lean_ctor_get(v___y_191_, 0);
v_fileMap_198_ = lean_ctor_get(v___y_191_, 1);
v___x_199_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_143_);
v___x_200_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v___x_199_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_214_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_inc_ref_n(v_fileMap_198_, 2);
v___x_205_ = l_Lean_FileMap_toPosition(v_fileMap_198_, v___y_193_);
lean_dec(v___y_193_);
v___x_206_ = l_Lean_FileMap_toPosition(v_fileMap_198_, v___y_196_);
lean_dec(v___y_196_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
v___x_208_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_192_ == 0)
{
lean_del_object(v___x_203_);
lean_dec_ref(v___y_190_);
v___y_152_ = v_fileName_197_;
v___y_153_ = v___x_207_;
v___y_154_ = v___x_205_;
v___y_155_ = v___y_194_;
v___y_156_ = v___x_208_;
v___y_157_ = v___y_195_;
v___y_158_ = v_a_201_;
v_toCold_159_ = v___y_189_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
else
{
uint8_t v___x_209_; 
lean_inc(v_a_201_);
v___x_209_ = l_Lean_MessageData_hasTag(v___y_190_, v_a_201_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec_ref_known(v___x_207_, 1);
lean_dec_ref(v___x_205_);
lean_dec(v_a_201_);
v___x_210_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_210_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
else
{
lean_del_object(v___x_203_);
v___y_152_ = v_fileName_197_;
v___y_153_ = v___x_207_;
v___y_154_ = v___x_205_;
v___y_155_ = v___y_194_;
v___y_156_ = v___x_208_;
v___y_157_ = v___y_195_;
v___y_158_ = v_a_201_;
v_toCold_159_ = v___y_189_;
v___y_160_ = v___y_149_;
goto v___jp_151_;
}
}
}
}
v___jp_215_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Syntax_getTailPos_x3f(v___y_219_, v___y_221_);
lean_dec(v___y_219_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_inc(v___y_222_);
v___y_189_ = v___y_216_;
v___y_190_ = v___y_218_;
v___y_191_ = v___y_216_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_222_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_221_;
v___y_196_ = v___y_222_;
goto v___jp_188_;
}
else
{
lean_object* v_val_224_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
v___y_189_ = v___y_216_;
v___y_190_ = v___y_218_;
v___y_191_ = v___y_216_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_222_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_221_;
v___y_196_ = v_val_224_;
goto v___jp_188_;
}
}
v___jp_225_:
{
lean_object* v_toCold_229_; lean_object* v_ref_230_; uint8_t v_suppressElabErrors_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v_ref_235_; lean_object* v___x_236_; 
v_toCold_229_ = lean_ctor_get(v___y_148_, 0);
v_ref_230_ = lean_ctor_get(v___y_148_, 2);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v___y_148_, sizeof(void*)*3 + 2);
v___x_232_ = lean_box(v_suppressElabErrors_231_);
v___x_233_ = lean_box(v___y_226_);
v___f_234_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_234_, 0, v___x_232_);
lean_closure_set(v___f_234_, 1, v___x_233_);
v_ref_235_ = l_Lean_replaceRef(v_ref_142_, v_ref_230_);
v___x_236_ = l_Lean_Syntax_getPos_x3f(v_ref_235_, v___y_227_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_216_ = v_toCold_229_;
v___y_217_ = v_suppressElabErrors_231_;
v___y_218_ = v___f_234_;
v___y_219_ = v_ref_235_;
v___y_220_ = v___y_228_;
v___y_221_ = v___y_227_;
v___y_222_ = v___x_237_;
goto v___jp_215_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_236_, 1);
v___y_216_ = v_toCold_229_;
v___y_217_ = v_suppressElabErrors_231_;
v___y_218_ = v___f_234_;
v___y_219_ = v_ref_235_;
v___y_220_ = v___y_228_;
v___y_221_ = v___y_227_;
v___y_222_ = v_val_238_;
goto v___jp_215_;
}
}
v___jp_240_:
{
if (v___y_243_ == 0)
{
v___y_226_ = v___y_241_;
v___y_227_ = v___y_242_;
v___y_228_ = v_severity_144_;
goto v___jp_225_;
}
else
{
v___y_226_ = v___y_241_;
v___y_227_ = v___y_242_;
v___y_228_ = v___x_239_;
goto v___jp_225_;
}
}
v___jp_244_:
{
if (v___y_245_ == 0)
{
uint8_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 1;
v___x_247_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_246_);
if (v___x_247_ == 0)
{
v___y_241_ = v___y_245_;
v___y_242_ = v___y_245_;
v___y_243_ = v___x_247_;
goto v___jp_240_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_148_);
v___x_249_ = l_Lean_warningAsError;
v___x_250_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v___x_248_, v___x_249_);
lean_dec_ref(v___x_248_);
v___y_241_ = v___y_245_;
v___y_242_ = v___y_245_;
v___y_243_ = v___x_250_;
goto v___jp_240_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v_msgData_143_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_255_, lean_object* v_msgData_256_, lean_object* v_severity_257_, lean_object* v_isSilent_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v_severity_boxed_264_; uint8_t v_isSilent_boxed_265_; lean_object* v_res_266_; 
v_severity_boxed_264_ = lean_unbox(v_severity_257_);
v_isSilent_boxed_265_ = lean_unbox(v_isSilent_258_);
v_res_266_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_255_, v_msgData_256_, v_severity_boxed_264_, v_isSilent_boxed_265_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v_ref_255_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object* v_ref_267_, lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
uint8_t v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = 1;
v___x_279_ = 0;
v___x_280_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_267_, v_msgData_268_, v___x_278_, v___x_279_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object* v_ref_281_, lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_ref_281_, v_msgData_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v_ref_281_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object* v_linterOption_299_, lean_object* v_stx_300_, lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_name_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_329_; 
v_name_311_ = lean_ctor_get(v_linterOption_299_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_linterOption_299_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_linterOption_299_, 1);
lean_dec(v_unused_330_);
v___x_313_ = v_linterOption_299_;
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_name_311_);
lean_dec(v_linterOption_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1);
lean_inc(v_name_311_);
v___x_316_ = l_Lean_MessageData_ofName(v_name_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 7);
lean_ctor_set(v___x_313_, 1, v___x_316_);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_328_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_disable_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_319_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v_disable_321_ = l_Lean_MessageData_note(v___x_320_);
v___x_322_ = l_Lean_Linter_linterMessageTag;
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v_msg_301_);
lean_ctor_set(v___x_323_, 1, v_disable_321_);
v___x_324_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_325_, 0, v_name_311_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
lean_inc(v_stx_300_);
v___x_326_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_326_, 0, v_stx_300_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_stx_300_, v___x_326_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v_stx_300_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object* v_linterOption_331_, lean_object* v_stx_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v_linterOption_331_, v_stx_332_, v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object* v_o_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v___x_350_; lean_object* v_toEnvExtension_351_; lean_object* v_asyncMode_352_; lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v_merged_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v___x_347_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_348_ = lean_st_ref_get(v___y_345_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_env_349_);
lean_dec(v___x_348_);
v___x_350_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_351_ = lean_ctor_get(v___x_350_, 0);
v_asyncMode_352_ = lean_ctor_get(v_toEnvExtension_351_, 2);
v___x_353_ = lean_box(0);
v___x_354_ = 0;
v___x_355_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_347_, v___x_350_, v_env_349_, v_asyncMode_352_, v___x_353_, v___x_354_);
v_merged_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_355_, 1);
lean_dec(v_unused_365_);
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_merged_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_merged_356_);
lean_ctor_set(v___x_358_, 0, v_o_344_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_o_344_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_merged_356_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg___boxed(lean_object* v_o_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_366_, v___y_367_);
lean_dec(v___y_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_376_);
v___x_380_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v___x_379_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0___boxed(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5));
v___x_401_ = l_Lean_MessageData_ofFormat(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(lean_object* v_initialState_402_, lean_object* v_ref_403_, lean_object* v_replacement_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_462_; 
v___x_414_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_462_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = l_Lean_Elab_Tactic_linter_unnecessaryRwa;
v___x_420_ = l_Lean_Linter_getLinterValue(v___x_419_, v_a_415_);
lean_dec(v_a_415_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec(v_replacement_404_);
lean_dec(v_ref_403_);
lean_dec_ref(v_initialState_402_);
v___x_421_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_417_);
v___x_425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1);
v___x_426_ = lean_box(0);
lean_inc(v_replacement_404_);
v___x_427_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_402_, v_replacement_404_, v___x_426_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; uint8_t v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = lean_unbox(v_a_428_);
lean_dec(v_a_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_replacement_404_);
v___x_430_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_419_, v_ref_403_, v___x_425_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3));
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_replacement_404_);
v___x_433_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_426_);
lean_ctor_set(v___x_433_, 2, v___x_426_);
lean_ctor_set(v___x_433_, 3, v___x_426_);
lean_ctor_set(v___x_433_, 4, v___x_426_);
lean_ctor_set(v___x_433_, 5, v___x_426_);
lean_inc(v_ref_403_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_ref_403_);
v___x_435_ = 4;
lean_inc_ref(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_436_, 0, v___x_433_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_426_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*3, v___x_435_);
v___x_437_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_440_ = lean_array_push(v___x_439_, v___x_436_);
v___x_441_ = 0;
v___x_442_ = l_Lean_MessageData_hint(v___x_437_, v___x_440_, v___x_434_, v___x_426_, v___x_441_, v_a_411_, v_a_412_);
lean_dec_ref(v___x_440_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_425_);
lean_ctor_set(v___x_444_, 1, v_a_443_);
v___x_445_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_419_, v_ref_403_, v___x_444_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_ref_403_);
v_a_446_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_442_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_replacement_404_);
lean_dec(v_ref_403_);
v_a_454_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_427_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_427_);
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
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___boxed(lean_object* v_initialState_463_, lean_object* v_ref_464_, lean_object* v_replacement_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_initialState_463_, v_ref_464_, v_replacement_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(lean_object* v_o_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_476_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___boxed(lean_object* v_o_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(v_o_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(lean_object* v_ref_498_, lean_object* v_msgData_499_, uint8_t v_severity_500_, uint8_t v_isSilent_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_498_, v_msgData_499_, v_severity_500_, v_isSilent_501_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_512_, lean_object* v_msgData_513_, lean_object* v_severity_514_, lean_object* v_isSilent_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_severity_boxed_525_; uint8_t v_isSilent_boxed_526_; lean_object* v_res_527_; 
v_severity_boxed_525_ = lean_unbox(v_severity_514_);
v_isSilent_boxed_526_ = lean_unbox(v_isSilent_515_);
v_res_527_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(v_ref_512_, v_msgData_513_, v_severity_boxed_525_, v_isSilent_boxed_526_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v_ref_512_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_ref_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_ref_567_ = lean_ctor_get(v___y_564_, 2);
v___x_568_ = 0;
v___x_569_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_568_);
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
lean_inc_n(v___x_569_, 6);
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_569_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_569_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_Syntax_node1(v___x_569_, v___x_576_, v___x_578_);
v___x_580_ = l_Lean_Syntax_node1(v___x_569_, v___x_575_, v___x_579_);
v___x_581_ = l_Lean_Syntax_node1(v___x_569_, v___x_574_, v___x_580_);
v___x_582_ = l_Lean_Syntax_node1(v___x_569_, v___x_573_, v___x_581_);
v___x_583_ = l_Lean_Syntax_node2(v___x_569_, v___x_570_, v___x_572_, v___x_582_);
v___x_584_ = l_Lean_Elab_Tactic_evalTactic(v___x_583_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_594_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = 1;
v___x_589_ = lean_box(v___x_588_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_589_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_584_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed(lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(lean_object* v___f_613_, lean_object* v_close_614_, lean_object* v_a_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_617_, v___y_619_, v___y_621_, v___y_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_613_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec(v_a_626_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_close_614_);
return v___x_627_;
}
else
{
lean_object* v_a_628_; uint8_t v___y_630_; uint8_t v___x_658_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v___x_658_ = l_Lean_Exception_isInterrupt(v_a_628_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
lean_inc(v_a_628_);
v___x_659_ = l_Lean_Exception_isRuntime(v_a_628_);
v___y_630_ = v___x_659_;
goto v___jp_629_;
}
else
{
v___y_630_ = v___x_658_;
goto v___jp_629_;
}
v___jp_629_:
{
if (v___y_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref_known(v___x_627_, 1);
v___x_631_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_626_, v___y_630_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_632_; 
lean_dec_ref_known(v___x_631_, 1);
v___x_632_ = lean_apply_10(v_close_614_, v_a_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, lean_box(0));
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_641_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_box(v___y_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_632_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_632_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_close_614_);
v_a_650_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_631_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_631_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_dec(v_a_626_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_close_614_);
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_close_614_);
lean_dec_ref(v___f_613_);
v_a_660_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_625_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_625_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed(lean_object* v___f_668_, lean_object* v_close_669_, lean_object* v_a_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(v___f_668_, v_close_669_, v_a_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(lean_object* v_rewrite_718_, lean_object* v___f_719_, lean_object* v_close_720_, lean_object* v_ref_721_, lean_object* v_replacement_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_724_, v___y_726_, v___y_728_, v___y_730_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
v___x_797_ = lean_apply_9(v_rewrite_718_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___f_799_; lean_object* v___x_800_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___f_799_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_799_, 0, v___f_719_);
lean_closure_set(v___f_799_, 1, v_close_720_);
lean_closure_set(v___f_799_, 2, v_a_798_);
v___x_800_ = l_Lean_Elab_Tactic_focus___redArg(v___f_799_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_802_) == 0)
{
uint8_t v___x_803_; 
v___x_803_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_803_ == 0)
{
lean_dec_ref_known(v___x_802_, 1);
lean_dec(v_a_796_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
goto v___jp_732_;
}
else
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_802_, 1);
v___x_805_ = l_List_isEmpty___redArg(v_a_804_);
lean_dec(v_a_804_);
if (v___x_805_ == 0)
{
lean_dec(v_a_796_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
goto v___jp_732_;
}
else
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_a_796_, v_ref_721_, v_replacement_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_dec_ref_known(v___x_806_, 1);
goto v___jp_732_;
}
else
{
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_a_801_);
lean_dec(v_a_796_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
v_a_807_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_802_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_a_796_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
v_a_815_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_800_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_800_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_796_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
lean_dec_ref(v_close_720_);
lean_dec_ref(v___f_719_);
v_a_823_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_797_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_797_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
lean_dec_ref(v_close_720_);
lean_dec_ref(v___f_719_);
lean_dec_ref(v_rewrite_718_);
v_a_831_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_795_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_795_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
v___jp_732_:
{
lean_object* v_ref_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_ref_733_ = lean_ctor_get(v___y_729_, 2);
v___x_734_ = 0;
v___x_735_ = l_Lean_SourceInfo_fromRef(v_ref_733_, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1));
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2));
lean_inc_n(v___x_735_, 37);
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_735_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4));
v___x_743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5));
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_735_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6));
v___x_746_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_735_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9));
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_735_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_735_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_735_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v___x_735_, v___x_754_, v___x_756_);
v___x_758_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node2(v___x_735_, v___x_751_, v___x_753_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_763_);
lean_inc_ref_n(v___x_750_, 2);
v___x_765_ = l_Lean_Syntax_node2(v___x_735_, v___x_748_, v___x_750_, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_735_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
v___x_769_ = l_Lean_Syntax_node1(v___x_735_, v___x_767_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___x_735_, v___x_748_, v___x_750_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13));
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_735_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
v___x_777_ = l_Lean_Syntax_node1(v___x_735_, v___x_775_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node2(v___x_735_, v___x_748_, v___x_750_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node3(v___x_735_, v___x_741_, v___x_765_, v___x_773_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v___x_735_, v___x_746_, v___x_747_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_785_);
v___x_787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_735_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_Syntax_node3(v___x_735_, v___x_742_, v___x_744_, v___x_786_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node1(v___x_735_, v___x_741_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node1(v___x_735_, v___x_740_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node1(v___x_735_, v___x_739_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node2(v___x_735_, v___x_736_, v___x_738_, v___x_792_);
v___x_794_ = l_Lean_Elab_Tactic_evalTactic(v___x_793_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object* v_rewrite_839_, lean_object* v___f_840_, lean_object* v_close_841_, lean_object* v_ref_842_, lean_object* v_replacement_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(v_rewrite_839_, v___f_840_, v_close_841_, v_ref_842_, v_replacement_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object* v_ref_855_, lean_object* v_rewrite_856_, lean_object* v_replacement_857_, lean_object* v_close_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_870_; 
v___f_868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0));
v___f_869_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed), 14, 5);
lean_closure_set(v___f_869_, 0, v_rewrite_856_);
lean_closure_set(v___f_869_, 1, v___f_868_);
lean_closure_set(v___f_869_, 2, v_close_858_);
lean_closure_set(v___f_869_, 3, v_ref_855_);
lean_closure_set(v___f_869_, 4, v_replacement_857_);
v___x_870_ = l_Lean_Elab_Tactic_focus___redArg(v___f_869_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object* v_ref_871_, lean_object* v_rewrite_872_, lean_object* v_replacement_873_, lean_object* v_close_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_871_, v_rewrite_872_, v_replacement_873_, v_close_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object* v_00_u03b1_885_, lean_object* v_ref_886_, lean_object* v_rewrite_887_, lean_object* v_replacement_888_, lean_object* v_close_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_886_, v_rewrite_887_, v_replacement_888_, v_close_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object* v_00_u03b1_900_, lean_object* v_ref_901_, lean_object* v_rewrite_902_, lean_object* v_replacement_903_, lean_object* v_close_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(v_00_u03b1_900_, v_ref_901_, v_rewrite_902_, v_replacement_903_, v_close_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_ref_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_931_; 
v_ref_921_ = lean_ctor_get(v___y_918_, 2);
v___x_922_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
lean_inc(v_ref_921_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_ref_921_);
lean_ctor_set(v___x_927_, 1, v_a_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 1);
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object* v_fvarId_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_952_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___x_974_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = l_Lean_mkFVar(v_fvarId_950_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc_ref(v___x_962_);
v___x_974_ = lean_infer_type(v___x_962_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = l_Lean_MVarId_getType(v_a_961_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; uint8_t v_a_979_; lean_object* v___x_999_; uint8_t v_foApprox_1000_; uint8_t v_ctxApprox_1001_; uint8_t v_quasiPatternApprox_1002_; uint8_t v_constApprox_1003_; uint8_t v_isDefEqStuckEx_1004_; uint8_t v_unificationHints_1005_; uint8_t v_proofIrrelevance_1006_; uint8_t v_offsetCnstrs_1007_; uint8_t v_transparency_1008_; uint8_t v_etaStruct_1009_; uint8_t v_univApprox_1010_; uint8_t v_iota_1011_; uint8_t v_beta_1012_; uint8_t v_proj_1013_; uint8_t v_zeta_1014_; uint8_t v_zetaDelta_1015_; uint8_t v_zetaUnused_1016_; uint8_t v_zetaHave_1017_; uint8_t v_canUnfoldPredicateConfig_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1052_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_999_ = l_Lean_Meta_Context_config(v___y_955_);
v_foApprox_1000_ = lean_ctor_get_uint8(v___x_999_, 0);
v_ctxApprox_1001_ = lean_ctor_get_uint8(v___x_999_, 1);
v_quasiPatternApprox_1002_ = lean_ctor_get_uint8(v___x_999_, 2);
v_constApprox_1003_ = lean_ctor_get_uint8(v___x_999_, 3);
v_isDefEqStuckEx_1004_ = lean_ctor_get_uint8(v___x_999_, 4);
v_unificationHints_1005_ = lean_ctor_get_uint8(v___x_999_, 5);
v_proofIrrelevance_1006_ = lean_ctor_get_uint8(v___x_999_, 6);
v_offsetCnstrs_1007_ = lean_ctor_get_uint8(v___x_999_, 8);
v_transparency_1008_ = lean_ctor_get_uint8(v___x_999_, 9);
v_etaStruct_1009_ = lean_ctor_get_uint8(v___x_999_, 10);
v_univApprox_1010_ = lean_ctor_get_uint8(v___x_999_, 11);
v_iota_1011_ = lean_ctor_get_uint8(v___x_999_, 12);
v_beta_1012_ = lean_ctor_get_uint8(v___x_999_, 13);
v_proj_1013_ = lean_ctor_get_uint8(v___x_999_, 14);
v_zeta_1014_ = lean_ctor_get_uint8(v___x_999_, 15);
v_zetaDelta_1015_ = lean_ctor_get_uint8(v___x_999_, 16);
v_zetaUnused_1016_ = lean_ctor_get_uint8(v___x_999_, 17);
v_zetaHave_1017_ = lean_ctor_get_uint8(v___x_999_, 18);
v_canUnfoldPredicateConfig_1018_ = lean_ctor_get_uint8(v___x_999_, 19);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1020_ = v___x_999_;
v_isShared_1021_ = v_isSharedCheck_1052_;
goto v_resetjp_1019_;
}
else
{
lean_dec(v___x_999_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1052_;
goto v_resetjp_1019_;
}
v___jp_978_:
{
if (v_a_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2));
v___x_982_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_975_, v_a_977_, v___x_980_, v___x_981_, v___y_955_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4);
v___x_985_ = l_Lean_indentExpr(v___x_962_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v_a_983_);
v___x_990_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v___x_989_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v___x_990_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v___x_962_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
v_a_991_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_982_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_982_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_dec(v_a_977_);
lean_dec(v_a_975_);
v___y_964_ = v___y_952_;
v___y_965_ = v___y_953_;
v___y_966_ = v___y_954_;
v___y_967_ = v___y_955_;
v___y_968_ = v___y_956_;
v___y_969_ = v___y_957_;
v___y_970_ = v___y_958_;
goto v___jp_963_;
}
}
v_resetjp_1019_:
{
uint8_t v_trackZetaDelta_1022_; lean_object* v_zetaDeltaSet_1023_; lean_object* v_lctx_1024_; lean_object* v_localInstances_1025_; lean_object* v_defEqCtx_x3f_1026_; lean_object* v_synthPendingDepth_1027_; lean_object* v_customCanUnfoldPredicate_x3f_1028_; uint8_t v_univApprox_1029_; uint8_t v_inTypeClassResolution_1030_; uint8_t v_cacheInferType_1031_; uint8_t v___x_1032_; lean_object* v___x_1034_; 
v_trackZetaDelta_1022_ = lean_ctor_get_uint8(v___y_955_, sizeof(void*)*7);
v_zetaDeltaSet_1023_ = lean_ctor_get(v___y_955_, 1);
v_lctx_1024_ = lean_ctor_get(v___y_955_, 2);
v_localInstances_1025_ = lean_ctor_get(v___y_955_, 3);
v_defEqCtx_x3f_1026_ = lean_ctor_get(v___y_955_, 4);
v_synthPendingDepth_1027_ = lean_ctor_get(v___y_955_, 5);
v_customCanUnfoldPredicate_x3f_1028_ = lean_ctor_get(v___y_955_, 6);
v_univApprox_1029_ = lean_ctor_get_uint8(v___y_955_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1030_ = lean_ctor_get_uint8(v___y_955_, sizeof(void*)*7 + 2);
v_cacheInferType_1031_ = lean_ctor_get_uint8(v___y_955_, sizeof(void*)*7 + 3);
v___x_1032_ = 1;
if (v_isShared_1021_ == 0)
{
v___x_1034_ = v___x_1020_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 0, v_foApprox_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 1, v_ctxApprox_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 2, v_quasiPatternApprox_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 3, v_constApprox_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 4, v_isDefEqStuckEx_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 5, v_unificationHints_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 6, v_proofIrrelevance_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 8, v_offsetCnstrs_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 9, v_transparency_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 10, v_etaStruct_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 11, v_univApprox_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 12, v_iota_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 13, v_beta_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 14, v_proj_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 15, v_zeta_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 16, v_zetaDelta_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 17, v_zetaUnused_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 18, v_zetaHave_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, 19, v_canUnfoldPredicateConfig_1018_);
v___x_1034_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
uint64_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_ctor_set_uint8(v___x_1034_, 7, v___x_1032_);
v___x_1035_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set_uint64(v___x_1036_, sizeof(void*)*1, v___x_1035_);
lean_inc(v_customCanUnfoldPredicate_x3f_1028_);
lean_inc(v_synthPendingDepth_1027_);
lean_inc(v_defEqCtx_x3f_1026_);
lean_inc_ref(v_localInstances_1025_);
lean_inc_ref(v_lctx_1024_);
lean_inc(v_zetaDeltaSet_1023_);
v___x_1037_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v_zetaDeltaSet_1023_);
lean_ctor_set(v___x_1037_, 2, v_lctx_1024_);
lean_ctor_set(v___x_1037_, 3, v_localInstances_1025_);
lean_ctor_set(v___x_1037_, 4, v_defEqCtx_x3f_1026_);
lean_ctor_set(v___x_1037_, 5, v_synthPendingDepth_1027_);
lean_ctor_set(v___x_1037_, 6, v_customCanUnfoldPredicate_x3f_1028_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*7, v_trackZetaDelta_1022_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*7 + 1, v_univApprox_1029_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1030_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*7 + 3, v_cacheInferType_1031_);
lean_inc(v_a_977_);
lean_inc(v_a_975_);
v___x_1038_ = l_Lean_Meta_isExprDefEq(v_a_975_, v_a_977_, v___x_1037_, v___y_956_, v___y_957_, v___y_958_);
lean_dec_ref_known(v___x_1037_, 7);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; uint8_t v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = lean_unbox(v_a_1039_);
lean_dec(v_a_1039_);
v_a_979_ = v___x_1040_;
goto v___jp_978_;
}
else
{
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1041_; uint8_t v___x_1042_; 
v_a_1041_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1042_ = lean_unbox(v_a_1041_);
lean_dec(v_a_1041_);
v_a_979_ = v___x_1042_;
goto v___jp_978_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_977_);
lean_dec(v_a_975_);
lean_dec_ref(v___x_962_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
v_a_1043_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1038_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1038_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_975_);
lean_dec_ref(v___x_962_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
v_a_1053_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_976_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_976_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_962_);
lean_dec(v_a_961_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
v_a_1061_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_974_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_974_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
v___jp_963_:
{
lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1));
v___x_972_ = 1;
v___x_973_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_971_, v___x_962_, v___x_972_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v___x_973_;
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_fvarId_950_);
v_a_1069_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_960_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_960_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object* v_fvarId_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(v_fvarId_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object* v_fvarId_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___f_1098_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1098_, 0, v_fvarId_1088_);
v___x_1099_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1098_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object* v_fvarId_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(v_fvarId_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object* v_00_u03b1_1111_, lean_object* v_msg_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_1112_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object* v_00_u03b1_1123_, lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(v_00_u03b1_1123_, v_msg_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1134_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg(){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object* v_00_u03b1_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object* v_00_u03b1_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(v_00_u03b1_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_ref_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_ref_1174_ = lean_ctor_get(v___y_1171_, 2);
v___x_1175_ = 0;
v___x_1176_ = l_Lean_SourceInfo_fromRef(v_ref_1174_, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object* v___f_1188_, lean_object* v___x_1189_, lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1198_);
lean_inc_ref(v___y_1197_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
v___x_1202_ = lean_apply_9(v___f_1188_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, lean_box(0));
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_n(v_a_1203_, 2);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_1205_ = l_Lean_Name_mkStr4(v___x_1189_, v___x_1190_, v___x_1191_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_a_1203_);
lean_ctor_set(v___x_1206_, 1, v___x_1204_);
v___x_1207_ = l_Lean_Syntax_node1(v_a_1203_, v___x_1205_, v___x_1206_);
v___x_1208_ = l_Lean_Elab_Tactic_evalTactic(v___x_1207_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1208_;
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___x_1190_);
lean_dec_ref(v___x_1189_);
v_a_1209_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1202_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1202_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object* v___f_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v_x_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_Tactic_evalRwa___lam__1(v___f_1217_, v___x_1218_, v___x_1219_, v___x_1220_, v_x_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRwa___closed__10(void){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Array_mkArray0___redArg();
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object* v_stx_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
lean_inc(v_stx_1270_);
v___x_1281_ = l_Lean_Syntax_isOfKind(v_stx_1270_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_stx_1270_);
v___x_1282_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1284_);
v___x_1286_ = l_Lean_Syntax_isOfKind(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v___x_1284_);
lean_dec(v_stx_1270_);
v___x_1287_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1287_;
}
else
{
lean_object* v_ref_1288_; lean_object* v___f_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_ref_1288_ = lean_ctor_get(v_a_1277_, 2);
v___f_1289_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__4));
v___x_1290_ = 0;
v___x_1291_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__6));
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__7));
lean_inc_n(v___x_1291_, 3);
v___x_1294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1297_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1291_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_inc_ref(v___x_1298_);
v___x_1299_ = l_Lean_Syntax_node1(v___x_1291_, v___x_1295_, v___x_1298_);
lean_inc(v___x_1284_);
v___x_1300_ = l_Lean_Syntax_node4(v___x_1291_, v___x_1292_, v___x_1294_, v___x_1299_, v___x_1284_, v___x_1298_);
v___x_1301_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_n(v_a_1302_, 4);
lean_dec_ref(v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
v___x_1305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1305_, 0, v_a_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1306_, 0, v_a_1302_);
lean_ctor_set(v___x_1306_, 1, v___x_1296_);
lean_ctor_set(v___x_1306_, 2, v___x_1297_);
lean_inc_ref(v___x_1306_);
v___x_1307_ = l_Lean_Syntax_node1(v_a_1302_, v___x_1295_, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node4(v_a_1302_, v___x_1303_, v___x_1305_, v___x_1307_, v___x_1284_, v___x_1306_);
v___x_1309_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1309_, 0, v___x_1300_);
v___x_1310_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1270_, v___x_1309_, v___x_1308_, v___f_1289_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object* v_stx_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_Tactic_evalRwa(v_stx_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1(){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1));
v___x_1332_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwa___boxed), 10, 0);
v___x_1333_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1329_, v___x_1330_, v___x_1331_, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t v___x_1336_, lean_object* v_fvarId_1337_, uint8_t v_symm_1338_, lean_object* v_term_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1349_ = 2;
v___x_1350_ = lean_box(0);
v___x_1351_ = 0;
v___x_1352_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*1, v___x_1349_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*1 + 1, v___x_1336_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*1 + 2, v___x_1351_);
v___x_1353_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_term_1339_, v_symm_1338_, v_fvarId_1337_, v___x_1352_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object* v___x_1354_, lean_object* v_fvarId_1355_, lean_object* v_symm_1356_, lean_object* v_term_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v___x_2496__boxed_1367_; uint8_t v_symm_boxed_1368_; lean_object* v_res_1369_; 
v___x_2496__boxed_1367_ = lean_unbox(v___x_1354_);
v_symm_boxed_1368_ = lean_unbox(v_symm_1356_);
v_res_1369_ = l_Lean_Elab_Tactic_evalRwaAt___lam__0(v___x_2496__boxed_1367_, v_fvarId_1355_, v_symm_boxed_1368_, v_term_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object* v___x_1370_, lean_object* v_stx_1371_, lean_object* v___x_1372_, lean_object* v___x_1373_, lean_object* v___f_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Elab_Tactic_getFVarId(v___x_1370_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Syntax_getArg(v_stx_1371_, v___x_1372_);
v___x_1387_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v___x_1386_, v___x_1373_, v_a_1385_, v___f_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1387_;
}
else
{
lean_dec_ref(v___f_1374_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object* v___x_1388_, lean_object* v_stx_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___f_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Elab_Tactic_evalRwaAt___lam__1(v___x_1388_, v_stx_1389_, v___x_1390_, v___x_1391_, v___f_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___x_1391_);
lean_dec(v___x_1390_);
lean_dec(v_stx_1389_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object* v_stx_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
lean_inc(v_stx_1423_);
v___x_1434_ = l_Lean_Syntax_isOfKind(v_stx_1423_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_stx_1423_);
v___x_1435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = l_Lean_Syntax_getArg(v_stx_1423_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1437_);
v___x_1439_ = l_Lean_Syntax_isOfKind(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v___x_1437_);
lean_dec(v_stx_1423_);
v___x_1440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1440_;
}
else
{
lean_object* v_ref_1441_; lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_ref_1441_ = lean_ctor_get(v_a_1430_, 2);
v___x_1442_ = lean_box(v___x_1439_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1443_, 0, v___x_1442_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = l_Lean_Syntax_getArg(v_stx_1423_, v___x_1445_);
lean_inc(v___x_1437_);
lean_inc(v_stx_1423_);
lean_inc(v___x_1446_);
v___f_1447_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1447_, 0, v___x_1446_);
lean_closure_set(v___f_1447_, 1, v_stx_1423_);
lean_closure_set(v___f_1447_, 2, v___x_1444_);
lean_closure_set(v___f_1447_, 3, v___x_1437_);
lean_closure_set(v___f_1447_, 4, v___f_1443_);
v___x_1448_ = 0;
v___x_1449_ = l_Lean_SourceInfo_fromRef(v_ref_1441_, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
lean_inc_n(v___x_1449_, 8);
v___x_1452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1449_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v___x_1455_);
v___x_1457_ = l_Lean_Syntax_node1(v___x_1449_, v___x_1453_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__3));
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__4));
v___x_1460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1449_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__6));
v___x_1462_ = l_Lean_Syntax_node1(v___x_1449_, v___x_1454_, v___x_1446_);
v___x_1463_ = l_Lean_Syntax_node1(v___x_1449_, v___x_1461_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node2(v___x_1449_, v___x_1458_, v___x_1460_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node1(v___x_1449_, v___x_1454_, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node4(v___x_1449_, v___x_1450_, v___x_1452_, v___x_1457_, v___x_1437_, v___x_1465_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__7));
v___x_1468_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1423_, v___f_1447_, v___x_1466_, v___x_1467_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object* v_stx_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Elab_Tactic_evalRwaAt(v_stx_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1(){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1487_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1488_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
v___x_1489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1));
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___boxed), 10, 0);
v___x_1491_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1487_, v___x_1488_, v___x_1489_, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
return v_res_1493_;
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
