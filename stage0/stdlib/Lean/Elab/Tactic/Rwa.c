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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_env_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_env_82_);
lean_dec(v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_77_);
v_toCold_84_ = lean_ctor_get(v___y_78_, 0);
v_mctx_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_83_);
v_lctx_86_ = lean_ctor_get(v___y_76_, 2);
v_options_87_ = lean_ctor_get(v_toCold_84_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_82_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_75_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_104_, uint8_t v___y_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 1)
{
lean_object* v_pre_107_; 
v_pre_107_ = lean_ctor_get(v_x_106_, 0);
switch(lean_obj_tag(v_pre_107_))
{
case 1:
{
lean_object* v_pre_108_; 
v_pre_108_ = lean_ctor_get(v_pre_107_, 0);
switch(lean_obj_tag(v_pre_108_))
{
case 0:
{
lean_object* v_str_109_; lean_object* v_str_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_str_109_ = lean_ctor_get(v_x_106_, 1);
v_str_110_ = lean_ctor_get(v_pre_107_, 1);
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_112_ = lean_string_dec_eq(v_str_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_114_ = lean_string_dec_eq(v_str_110_, v___x_113_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_116_ = lean_string_dec_eq(v_str_109_, v___x_115_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
return v_suppressElabErrors_104_;
}
}
}
else
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_118_ = lean_string_dec_eq(v_str_109_, v___x_117_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
return v_suppressElabErrors_104_;
}
}
}
case 1:
{
lean_object* v_pre_119_; 
v_pre_119_ = lean_ctor_get(v_pre_108_, 0);
if (lean_obj_tag(v_pre_119_) == 0)
{
lean_object* v_str_120_; lean_object* v_str_121_; lean_object* v_str_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_str_120_ = lean_ctor_get(v_x_106_, 1);
v_str_121_ = lean_ctor_get(v_pre_107_, 1);
v_str_122_ = lean_ctor_get(v_pre_108_, 1);
v___x_123_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_124_ = lean_string_dec_eq(v_str_122_, v___x_123_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_126_ = lean_string_dec_eq(v_str_121_, v___x_125_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_128_ = lean_string_dec_eq(v_str_120_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
return v_suppressElabErrors_104_;
}
}
}
}
else
{
return v___y_105_;
}
}
default: 
{
return v___y_105_;
}
}
}
case 0:
{
lean_object* v_str_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_str_129_ = lean_ctor_get(v_x_106_, 1);
v___x_130_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_131_ = lean_string_dec_eq(v_str_129_, v___x_130_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
return v_suppressElabErrors_104_;
}
}
default: 
{
return v___y_105_;
}
}
}
else
{
return v___y_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_132_, lean_object* v___y_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_suppressElabErrors_boxed_135_; uint8_t v___y_5672__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_suppressElabErrors_boxed_135_ = lean_unbox(v_suppressElabErrors_132_);
v___y_5672__boxed_136_ = lean_unbox(v___y_133_);
v_res_137_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_135_, v___y_5672__boxed_136_, v_x_134_);
lean_dec(v_x_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_140_, lean_object* v_msgData_141_, uint8_t v_severity_142_, uint8_t v_isSilent_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; lean_object* v_toCold_157_; lean_object* v___y_158_; lean_object* v___y_187_; lean_object* v___y_188_; uint8_t v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; lean_object* v___y_214_; lean_object* v___y_215_; uint8_t v___y_216_; uint8_t v___y_217_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; uint8_t v___x_237_; uint8_t v___y_239_; uint8_t v___y_240_; uint8_t v___y_241_; uint8_t v___y_243_; uint8_t v___x_251_; 
v___x_237_ = 2;
v___x_251_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_237_);
if (v___x_251_ == 0)
{
v___y_243_ = v___x_251_;
goto v___jp_242_;
}
else
{
uint8_t v___x_252_; 
lean_inc_ref(v_msgData_141_);
v___x_252_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_141_);
v___y_243_ = v___x_252_;
goto v___jp_242_;
}
v___jp_149_:
{
lean_object* v_currNamespace_159_; lean_object* v_openDecls_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_traceState_169_; lean_object* v_cache_170_; lean_object* v_recordedDeps_171_; lean_object* v_messages_172_; lean_object* v_infoState_173_; lean_object* v_snapshotTasks_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_185_; 
v_currNamespace_159_ = lean_ctor_get(v_toCold_157_, 4);
v_openDecls_160_ = lean_ctor_get(v_toCold_157_, 5);
lean_inc(v_openDecls_160_);
lean_inc(v_currNamespace_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_currNamespace_159_);
lean_ctor_set(v___x_161_, 1, v_openDecls_160_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___y_156_);
lean_inc_ref(v___y_152_);
lean_inc_ref(v___y_153_);
v___x_163_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_163_, 0, v___y_153_);
lean_ctor_set(v___x_163_, 1, v___y_154_);
lean_ctor_set(v___x_163_, 2, v___y_151_);
lean_ctor_set(v___x_163_, 3, v___y_152_);
lean_ctor_set(v___x_163_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5, v___y_155_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5 + 1, v___y_150_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5 + 2, v_isSilent_143_);
v___x_164_ = lean_st_ref_take(v___y_158_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
v_nextMacroScope_166_ = lean_ctor_get(v___x_164_, 1);
v_ngen_167_ = lean_ctor_get(v___x_164_, 2);
v_auxDeclNGen_168_ = lean_ctor_get(v___x_164_, 3);
v_traceState_169_ = lean_ctor_get(v___x_164_, 4);
v_cache_170_ = lean_ctor_get(v___x_164_, 5);
v_recordedDeps_171_ = lean_ctor_get(v___x_164_, 6);
v_messages_172_ = lean_ctor_get(v___x_164_, 7);
v_infoState_173_ = lean_ctor_get(v___x_164_, 8);
v_snapshotTasks_174_ = lean_ctor_get(v___x_164_, 9);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
v___x_176_ = v___x_164_;
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_snapshotTasks_174_);
lean_inc(v_infoState_173_);
lean_inc(v_messages_172_);
lean_inc(v_recordedDeps_171_);
lean_inc(v_cache_170_);
lean_inc(v_traceState_169_);
lean_inc(v_auxDeclNGen_168_);
lean_inc(v_ngen_167_);
lean_inc(v_nextMacroScope_166_);
lean_inc(v_env_165_);
lean_dec(v___x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_MessageLog_add(v___x_163_, v_messages_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 7, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_env_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v_cache_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v_recordedDeps_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_infoState_173_);
lean_ctor_set(v_reuseFailAlloc_184_, 9, v_snapshotTasks_174_);
v___x_181_ = v_reuseFailAlloc_184_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_st_ref_put(v___y_158_, v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_178_);
return v___x_183_;
}
}
}
v___jp_186_:
{
lean_object* v_fileName_195_; lean_object* v_fileMap_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
v_fileName_195_ = lean_ctor_get(v___y_190_, 0);
v_fileMap_196_ = lean_ctor_get(v___y_190_, 1);
v___x_197_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_141_);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v___x_197_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref_n(v_fileMap_196_, 2);
v___x_203_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_191_);
lean_dec(v___y_191_);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_194_);
lean_dec(v___y_194_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_193_ == 0)
{
lean_del_object(v___x_201_);
lean_dec_ref(v___y_188_);
v___y_150_ = v___y_189_;
v___y_151_ = v___x_205_;
v___y_152_ = v___x_206_;
v___y_153_ = v_fileName_195_;
v___y_154_ = v___x_203_;
v___y_155_ = v___y_192_;
v___y_156_ = v_a_199_;
v_toCold_157_ = v___y_187_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
else
{
uint8_t v___x_207_; 
lean_inc(v_a_199_);
v___x_207_ = l_Lean_MessageData_hasTag(v___y_188_, v_a_199_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec_ref_known(v___x_205_, 1);
lean_dec_ref(v___x_203_);
lean_dec(v_a_199_);
v___x_208_ = lean_box(0);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_150_ = v___y_189_;
v___y_151_ = v___x_205_;
v___y_152_ = v___x_206_;
v___y_153_ = v_fileName_195_;
v___y_154_ = v___x_203_;
v___y_155_ = v___y_192_;
v___y_156_ = v_a_199_;
v_toCold_157_ = v___y_187_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
}
}
}
v___jp_213_:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_218_, v___y_219_);
lean_dec(v___y_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_187_ = v___y_214_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_220_;
v___y_192_ = v___y_219_;
v___y_193_ = v___y_216_;
v___y_194_ = v___y_220_;
goto v___jp_186_;
}
else
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___y_187_ = v___y_214_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_220_;
v___y_192_ = v___y_219_;
v___y_193_ = v___y_216_;
v___y_194_ = v_val_222_;
goto v___jp_186_;
}
}
v___jp_223_:
{
lean_object* v_toCold_227_; lean_object* v_ref_228_; uint8_t v_suppressElabErrors_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v_ref_233_; lean_object* v___x_234_; 
v_toCold_227_ = lean_ctor_get(v___y_146_, 0);
v_ref_228_ = lean_ctor_get(v___y_146_, 2);
v_suppressElabErrors_229_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 2);
v___x_230_ = lean_box(v_suppressElabErrors_229_);
v___x_231_ = lean_box(v___y_224_);
v___f_232_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_232_, 0, v___x_230_);
lean_closure_set(v___f_232_, 1, v___x_231_);
v_ref_233_ = l_Lean_replaceRef(v_ref_140_, v_ref_228_);
v___x_234_ = l_Lean_Syntax_getPos_x3f(v_ref_233_, v___y_225_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___y_214_ = v_toCold_227_;
v___y_215_ = v___f_232_;
v___y_216_ = v_suppressElabErrors_229_;
v___y_217_ = v___y_226_;
v___y_218_ = v_ref_233_;
v___y_219_ = v___y_225_;
v___y_220_ = v___x_235_;
goto v___jp_213_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_234_, 1);
v___y_214_ = v_toCold_227_;
v___y_215_ = v___f_232_;
v___y_216_ = v_suppressElabErrors_229_;
v___y_217_ = v___y_226_;
v___y_218_ = v_ref_233_;
v___y_219_ = v___y_225_;
v___y_220_ = v_val_236_;
goto v___jp_213_;
}
}
v___jp_238_:
{
if (v___y_241_ == 0)
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_240_;
v___y_226_ = v_severity_142_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_240_;
v___y_226_ = v___x_237_;
goto v___jp_223_;
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 1;
v___x_245_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_244_);
if (v___x_245_ == 0)
{
v___y_239_ = v___y_243_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_245_;
goto v___jp_238_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_146_);
v___x_247_ = l_Lean_warningAsError;
v___x_248_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v___x_246_, v___x_247_);
lean_dec_ref(v___x_246_);
v___y_239_ = v___y_243_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_248_;
goto v___jp_238_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_msgData_141_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_253_, lean_object* v_msgData_254_, lean_object* v_severity_255_, lean_object* v_isSilent_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v_severity_boxed_262_; uint8_t v_isSilent_boxed_263_; lean_object* v_res_264_; 
v_severity_boxed_262_ = lean_unbox(v_severity_255_);
v_isSilent_boxed_263_ = lean_unbox(v_isSilent_256_);
v_res_264_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_253_, v_msgData_254_, v_severity_boxed_262_, v_isSilent_boxed_263_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v_ref_253_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object* v_ref_265_, lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = 1;
v___x_277_ = 0;
v___x_278_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_265_, v_msgData_266_, v___x_276_, v___x_277_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object* v_ref_279_, lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_ref_279_, v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v_ref_279_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object* v_linterOption_297_, lean_object* v_stx_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_name_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_327_; 
v_name_309_ = lean_ctor_get(v_linterOption_297_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_linterOption_297_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_linterOption_297_, 1);
lean_dec(v_unused_328_);
v___x_311_ = v_linterOption_297_;
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_name_309_);
lean_dec(v_linterOption_297_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1);
lean_inc(v_name_309_);
v___x_314_ = l_Lean_MessageData_ofName(v_name_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 7);
lean_ctor_set(v___x_311_, 1, v___x_314_);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_326_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_disable_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_317_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v_disable_319_ = l_Lean_MessageData_note(v___x_318_);
v___x_320_ = l_Lean_Linter_linterMessageTag;
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v_msg_299_);
lean_ctor_set(v___x_321_, 1, v_disable_319_);
v___x_322_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_323_, 0, v_name_309_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v_stx_298_);
v___x_324_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_324_, 0, v_stx_298_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_stx_298_, v___x_324_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v_stx_298_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object* v_linterOption_329_, lean_object* v_stx_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v_linterOption_329_, v_stx_330_, v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object* v_o_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v___x_348_; lean_object* v_toEnvExtension_349_; lean_object* v_asyncMode_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_merged_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
v___x_345_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_346_ = lean_st_ref_get(v___y_343_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_349_ = lean_ctor_get(v___x_348_, 0);
v_asyncMode_350_ = lean_ctor_get(v_toEnvExtension_349_, 2);
v___x_351_ = lean_box(0);
v___x_352_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_345_, v___x_348_, v_env_347_, v_asyncMode_350_, v___x_351_);
v_merged_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_352_, 1);
lean_dec(v_unused_362_);
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_merged_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_merged_353_);
lean_ctor_set(v___x_355_, 0, v_o_342_);
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_o_342_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_merged_353_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg___boxed(lean_object* v_o_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_363_, v___y_364_);
lean_dec(v___y_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_373_);
v___x_377_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v___x_376_, v___y_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0___boxed(lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5));
v___x_398_ = l_Lean_MessageData_ofFormat(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(lean_object* v_initialState_399_, lean_object* v_ref_400_, lean_object* v_replacement_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_459_; 
v___x_411_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_459_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_459_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_459_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = l_Lean_Elab_Tactic_linter_unnecessaryRwa;
v___x_417_ = l_Lean_Linter_getLinterValue(v___x_416_, v_a_412_);
lean_dec(v_a_412_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_replacement_401_);
lean_dec(v_ref_400_);
lean_dec_ref(v_initialState_399_);
v___x_418_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_418_);
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_del_object(v___x_414_);
v___x_422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1);
v___x_423_ = lean_box(0);
lean_inc(v_replacement_401_);
v___x_424_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_399_, v_replacement_401_, v___x_423_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; uint8_t v___x_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = lean_unbox(v_a_425_);
lean_dec(v_a_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec(v_replacement_401_);
v___x_427_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_416_, v_ref_400_, v___x_422_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3));
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_replacement_401_);
v___x_430_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_423_);
lean_ctor_set(v___x_430_, 2, v___x_423_);
lean_ctor_set(v___x_430_, 3, v___x_423_);
lean_ctor_set(v___x_430_, 4, v___x_423_);
lean_ctor_set(v___x_430_, 5, v___x_423_);
lean_inc(v_ref_400_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_ref_400_);
v___x_432_ = 4;
lean_inc_ref(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_433_, 0, v___x_430_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
lean_ctor_set(v___x_433_, 2, v___x_423_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*3, v___x_432_);
v___x_434_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = lean_array_push(v___x_436_, v___x_433_);
v___x_438_ = 0;
v___x_439_ = l_Lean_MessageData_hint(v___x_434_, v___x_437_, v___x_431_, v___x_423_, v___x_438_, v_a_408_, v_a_409_);
lean_dec_ref(v___x_437_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_422_);
lean_ctor_set(v___x_441_, 1, v_a_440_);
v___x_442_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_416_, v_ref_400_, v___x_441_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_ref_400_);
v_a_443_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_439_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_439_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
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
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_replacement_401_);
lean_dec(v_ref_400_);
v_a_451_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_424_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_424_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___boxed(lean_object* v_initialState_460_, lean_object* v_ref_461_, lean_object* v_replacement_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_initialState_460_, v_ref_461_, v_replacement_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(lean_object* v_o_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_473_, v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___boxed(lean_object* v_o_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(v_o_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(lean_object* v_ref_495_, lean_object* v_msgData_496_, uint8_t v_severity_497_, uint8_t v_isSilent_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_495_, v_msgData_496_, v_severity_497_, v_isSilent_498_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_509_, lean_object* v_msgData_510_, lean_object* v_severity_511_, lean_object* v_isSilent_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
uint8_t v_severity_boxed_522_; uint8_t v_isSilent_boxed_523_; lean_object* v_res_524_; 
v_severity_boxed_522_ = lean_unbox(v_severity_511_);
v_isSilent_boxed_523_ = lean_unbox(v_isSilent_512_);
v_res_524_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(v_ref_509_, v_msgData_510_, v_severity_boxed_522_, v_isSilent_boxed_523_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v_ref_509_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_ref_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_ref_564_ = lean_ctor_get(v___y_561_, 2);
v___x_565_ = 0;
v___x_566_ = l_Lean_SourceInfo_fromRef(v_ref_564_, v___x_565_);
v___x_567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
lean_inc_n(v___x_566_, 6);
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_566_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_Syntax_node1(v___x_566_, v___x_573_, v___x_575_);
v___x_577_ = l_Lean_Syntax_node1(v___x_566_, v___x_572_, v___x_576_);
v___x_578_ = l_Lean_Syntax_node1(v___x_566_, v___x_571_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node1(v___x_566_, v___x_570_, v___x_578_);
v___x_580_ = l_Lean_Syntax_node2(v___x_566_, v___x_567_, v___x_569_, v___x_579_);
v___x_581_ = l_Lean_Elab_Tactic_evalTactic(v___x_580_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_591_);
v___x_583_ = v___x_581_;
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
else
{
lean_dec(v___x_581_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = 1;
v___x_586_ = lean_box(v___x_585_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_581_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed(lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(lean_object* v___f_610_, lean_object* v_close_611_, lean_object* v_a_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_614_, v___y_616_, v___y_618_, v___y_620_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_610_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec(v_a_623_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_close_611_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; uint8_t v___y_627_; uint8_t v___x_655_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_625_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_Exception_isRuntime(v_a_625_);
v___y_627_ = v___x_656_;
goto v___jp_626_;
}
else
{
lean_dec(v_a_625_);
v___y_627_ = v___x_655_;
goto v___jp_626_;
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref_known(v___x_624_, 1);
v___x_628_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_623_, v___y_627_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_629_; 
lean_dec_ref_known(v___x_628_, 1);
v___x_629_ = lean_apply_10(v_close_611_, v_a_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_629_, 0);
lean_dec(v_unused_638_);
v___x_631_ = v___x_629_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_dec(v___x_629_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_box(v___y_627_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_a_639_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_629_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_629_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_close_611_);
v_a_647_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_628_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_628_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
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
else
{
lean_dec(v_a_623_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_close_611_);
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_close_611_);
lean_dec_ref(v___f_610_);
v_a_657_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_622_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_622_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed(lean_object* v___f_665_, lean_object* v_close_666_, lean_object* v_a_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(v___f_665_, v_close_666_, v_a_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(lean_object* v_rewrite_715_, lean_object* v___f_716_, lean_object* v_close_717_, lean_object* v_ref_718_, lean_object* v_replacement_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_721_, v___y_723_, v___y_725_, v___y_727_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_794_ = lean_apply_9(v_rewrite_715_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, lean_box(0));
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___f_796_; lean_object* v___x_797_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v___f_796_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_796_, 0, v___f_716_);
lean_closure_set(v___f_796_, 1, v_close_717_);
lean_closure_set(v___f_796_, 2, v_a_795_);
v___x_797_ = l_Lean_Elab_Tactic_focus___redArg(v___f_796_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_799_) == 0)
{
uint8_t v___x_800_; 
v___x_800_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
if (v___x_800_ == 0)
{
lean_dec_ref_known(v___x_799_, 1);
lean_dec(v_a_793_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
goto v___jp_729_;
}
else
{
lean_object* v_a_801_; uint8_t v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_799_, 1);
v___x_802_ = l_List_isEmpty___redArg(v_a_801_);
lean_dec(v_a_801_);
if (v___x_802_ == 0)
{
lean_dec(v_a_793_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
goto v___jp_729_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_a_793_, v_ref_718_, v_replacement_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_dec_ref_known(v___x_803_, 1);
goto v___jp_729_;
}
else
{
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_798_);
lean_dec(v_a_793_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
v_a_804_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_799_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
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
lean_dec(v_a_793_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
v_a_812_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_797_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_797_);
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
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_a_793_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
lean_dec_ref(v_close_717_);
lean_dec_ref(v___f_716_);
v_a_820_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_794_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_794_);
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
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_replacement_719_);
lean_dec(v_ref_718_);
lean_dec_ref(v_close_717_);
lean_dec_ref(v___f_716_);
lean_dec_ref(v_rewrite_715_);
v_a_828_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_792_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_792_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
v___jp_729_:
{
lean_object* v_ref_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_ref_730_ = lean_ctor_get(v___y_726_, 2);
v___x_731_ = 0;
v___x_732_ = l_Lean_SourceInfo_fromRef(v_ref_730_, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1));
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2));
lean_inc_n(v___x_732_, 37);
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_732_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4));
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_732_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6));
v___x_743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7));
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_732_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9));
v___x_746_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_732_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_732_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_732_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v___x_732_, v___x_751_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_756_);
v___x_758_ = l_Lean_Syntax_node2(v___x_732_, v___x_748_, v___x_750_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_760_);
lean_inc_ref_n(v___x_747_, 2);
v___x_762_ = l_Lean_Syntax_node2(v___x_732_, v___x_745_, v___x_747_, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_732_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
v___x_766_ = l_Lean_Syntax_node1(v___x_732_, v___x_764_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___x_732_, v___x_745_, v___x_747_, v___x_769_);
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13));
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_732_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
v___x_774_ = l_Lean_Syntax_node1(v___x_732_, v___x_772_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node2(v___x_732_, v___x_745_, v___x_747_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node3(v___x_732_, v___x_738_, v___x_762_, v___x_770_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v___x_732_, v___x_743_, v___x_744_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15));
v___x_785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_732_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_Syntax_node3(v___x_732_, v___x_739_, v___x_741_, v___x_783_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node1(v___x_732_, v___x_738_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node1(v___x_732_, v___x_737_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v___x_732_, v___x_736_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v___x_732_, v___x_733_, v___x_735_, v___x_789_);
v___x_791_ = l_Lean_Elab_Tactic_evalTactic(v___x_790_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object* v_rewrite_836_, lean_object* v___f_837_, lean_object* v_close_838_, lean_object* v_ref_839_, lean_object* v_replacement_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(v_rewrite_836_, v___f_837_, v_close_838_, v_ref_839_, v_replacement_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object* v_ref_852_, lean_object* v_rewrite_853_, lean_object* v_replacement_854_, lean_object* v_close_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v___f_865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0));
v___f_866_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed), 14, 5);
lean_closure_set(v___f_866_, 0, v_rewrite_853_);
lean_closure_set(v___f_866_, 1, v___f_865_);
lean_closure_set(v___f_866_, 2, v_close_855_);
lean_closure_set(v___f_866_, 3, v_ref_852_);
lean_closure_set(v___f_866_, 4, v_replacement_854_);
v___x_867_ = l_Lean_Elab_Tactic_focus___redArg(v___f_866_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object* v_ref_868_, lean_object* v_rewrite_869_, lean_object* v_replacement_870_, lean_object* v_close_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_868_, v_rewrite_869_, v_replacement_870_, v_close_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object* v_00_u03b1_882_, lean_object* v_ref_883_, lean_object* v_rewrite_884_, lean_object* v_replacement_885_, lean_object* v_close_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_883_, v_rewrite_884_, v_replacement_885_, v_close_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object* v_00_u03b1_897_, lean_object* v_ref_898_, lean_object* v_rewrite_899_, lean_object* v_replacement_900_, lean_object* v_close_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(v_00_u03b1_897_, v_ref_898_, v_rewrite_899_, v_replacement_900_, v_close_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_928_; 
v_ref_918_ = lean_ctor_get(v___y_915_, 2);
v___x_919_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msg_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_928_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
lean_inc(v_ref_918_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_ref_918_);
lean_ctor_set(v___x_924_, 1, v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_935_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object* v_fvarId_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_949_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___x_971_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l_Lean_mkFVar(v_fvarId_947_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc_ref(v___x_959_);
v___x_971_ = lean_infer_type(v___x_959_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_MVarId_getType(v_a_958_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; uint8_t v_a_976_; lean_object* v___x_996_; uint8_t v_foApprox_997_; uint8_t v_ctxApprox_998_; uint8_t v_quasiPatternApprox_999_; uint8_t v_constApprox_1000_; uint8_t v_isDefEqStuckEx_1001_; uint8_t v_unificationHints_1002_; uint8_t v_proofIrrelevance_1003_; uint8_t v_offsetCnstrs_1004_; uint8_t v_transparency_1005_; uint8_t v_etaStruct_1006_; uint8_t v_univApprox_1007_; uint8_t v_iota_1008_; uint8_t v_beta_1009_; uint8_t v_proj_1010_; uint8_t v_zeta_1011_; uint8_t v_zetaDelta_1012_; uint8_t v_zetaUnused_1013_; uint8_t v_zetaHave_1014_; uint8_t v_canUnfoldPredicateConfig_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1049_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_996_ = l_Lean_Meta_Context_config(v___y_952_);
v_foApprox_997_ = lean_ctor_get_uint8(v___x_996_, 0);
v_ctxApprox_998_ = lean_ctor_get_uint8(v___x_996_, 1);
v_quasiPatternApprox_999_ = lean_ctor_get_uint8(v___x_996_, 2);
v_constApprox_1000_ = lean_ctor_get_uint8(v___x_996_, 3);
v_isDefEqStuckEx_1001_ = lean_ctor_get_uint8(v___x_996_, 4);
v_unificationHints_1002_ = lean_ctor_get_uint8(v___x_996_, 5);
v_proofIrrelevance_1003_ = lean_ctor_get_uint8(v___x_996_, 6);
v_offsetCnstrs_1004_ = lean_ctor_get_uint8(v___x_996_, 8);
v_transparency_1005_ = lean_ctor_get_uint8(v___x_996_, 9);
v_etaStruct_1006_ = lean_ctor_get_uint8(v___x_996_, 10);
v_univApprox_1007_ = lean_ctor_get_uint8(v___x_996_, 11);
v_iota_1008_ = lean_ctor_get_uint8(v___x_996_, 12);
v_beta_1009_ = lean_ctor_get_uint8(v___x_996_, 13);
v_proj_1010_ = lean_ctor_get_uint8(v___x_996_, 14);
v_zeta_1011_ = lean_ctor_get_uint8(v___x_996_, 15);
v_zetaDelta_1012_ = lean_ctor_get_uint8(v___x_996_, 16);
v_zetaUnused_1013_ = lean_ctor_get_uint8(v___x_996_, 17);
v_zetaHave_1014_ = lean_ctor_get_uint8(v___x_996_, 18);
v_canUnfoldPredicateConfig_1015_ = lean_ctor_get_uint8(v___x_996_, 19);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1017_ = v___x_996_;
v_isShared_1018_ = v_isSharedCheck_1049_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_996_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1049_;
goto v_resetjp_1016_;
}
v___jp_975_:
{
if (v_a_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
v___x_978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2));
v___x_979_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_972_, v_a_974_, v___x_977_, v___x_978_, v___y_952_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4);
v___x_982_ = l_Lean_indentExpr(v___x_959_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v_a_980_);
v___x_987_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v___x_986_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_959_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
v_a_988_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_979_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_979_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_dec(v_a_974_);
lean_dec(v_a_972_);
v___y_961_ = v___y_949_;
v___y_962_ = v___y_950_;
v___y_963_ = v___y_951_;
v___y_964_ = v___y_952_;
v___y_965_ = v___y_953_;
v___y_966_ = v___y_954_;
v___y_967_ = v___y_955_;
goto v___jp_960_;
}
}
v_resetjp_1016_:
{
uint8_t v_trackZetaDelta_1019_; lean_object* v_zetaDeltaSet_1020_; lean_object* v_lctx_1021_; lean_object* v_localInstances_1022_; lean_object* v_defEqCtx_x3f_1023_; lean_object* v_synthPendingDepth_1024_; lean_object* v_customCanUnfoldPredicate_x3f_1025_; uint8_t v_univApprox_1026_; uint8_t v_inTypeClassResolution_1027_; uint8_t v_cacheInferType_1028_; uint8_t v___x_1029_; lean_object* v___x_1031_; 
v_trackZetaDelta_1019_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*7);
v_zetaDeltaSet_1020_ = lean_ctor_get(v___y_952_, 1);
v_lctx_1021_ = lean_ctor_get(v___y_952_, 2);
v_localInstances_1022_ = lean_ctor_get(v___y_952_, 3);
v_defEqCtx_x3f_1023_ = lean_ctor_get(v___y_952_, 4);
v_synthPendingDepth_1024_ = lean_ctor_get(v___y_952_, 5);
v_customCanUnfoldPredicate_x3f_1025_ = lean_ctor_get(v___y_952_, 6);
v_univApprox_1026_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1027_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*7 + 2);
v_cacheInferType_1028_ = lean_ctor_get_uint8(v___y_952_, sizeof(void*)*7 + 3);
v___x_1029_ = 1;
if (v_isShared_1018_ == 0)
{
v___x_1031_ = v___x_1017_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 0, v_foApprox_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 1, v_ctxApprox_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 2, v_quasiPatternApprox_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 3, v_constApprox_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 4, v_isDefEqStuckEx_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 5, v_unificationHints_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 6, v_proofIrrelevance_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 8, v_offsetCnstrs_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 9, v_transparency_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 10, v_etaStruct_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 11, v_univApprox_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 12, v_iota_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 13, v_beta_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 14, v_proj_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 15, v_zeta_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 16, v_zetaDelta_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 17, v_zetaUnused_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 18, v_zetaHave_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, 19, v_canUnfoldPredicateConfig_1015_);
v___x_1031_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
uint64_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_ctor_set_uint8(v___x_1031_, 7, v___x_1029_);
v___x_1032_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set_uint64(v___x_1033_, sizeof(void*)*1, v___x_1032_);
lean_inc(v_customCanUnfoldPredicate_x3f_1025_);
lean_inc(v_synthPendingDepth_1024_);
lean_inc(v_defEqCtx_x3f_1023_);
lean_inc_ref(v_localInstances_1022_);
lean_inc_ref(v_lctx_1021_);
lean_inc(v_zetaDeltaSet_1020_);
v___x_1034_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_zetaDeltaSet_1020_);
lean_ctor_set(v___x_1034_, 2, v_lctx_1021_);
lean_ctor_set(v___x_1034_, 3, v_localInstances_1022_);
lean_ctor_set(v___x_1034_, 4, v_defEqCtx_x3f_1023_);
lean_ctor_set(v___x_1034_, 5, v_synthPendingDepth_1024_);
lean_ctor_set(v___x_1034_, 6, v_customCanUnfoldPredicate_x3f_1025_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*7, v_trackZetaDelta_1019_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*7 + 1, v_univApprox_1026_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1027_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*7 + 3, v_cacheInferType_1028_);
lean_inc(v_a_974_);
lean_inc(v_a_972_);
v___x_1035_ = l_Lean_Meta_isExprDefEq(v_a_972_, v_a_974_, v___x_1034_, v___y_953_, v___y_954_, v___y_955_);
lean_dec_ref_known(v___x_1034_, 7);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; uint8_t v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = lean_unbox(v_a_1036_);
lean_dec(v_a_1036_);
v_a_976_ = v___x_1037_;
goto v___jp_975_;
}
else
{
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1038_; uint8_t v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1039_ = lean_unbox(v_a_1038_);
lean_dec(v_a_1038_);
v_a_976_ = v___x_1039_;
goto v___jp_975_;
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_974_);
lean_dec(v_a_972_);
lean_dec_ref(v___x_959_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
v_a_1040_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1035_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1035_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
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
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_972_);
lean_dec_ref(v___x_959_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
v_a_1050_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_973_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_973_);
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
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v___x_959_);
lean_dec(v_a_958_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
v_a_1058_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_971_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_971_);
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
v___jp_960_:
{
lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1));
v___x_969_ = 1;
v___x_970_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_968_, v___x_959_, v___x_969_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v___x_970_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v_fvarId_947_);
v_a_1066_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_957_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_957_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object* v_fvarId_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(v_fvarId_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object* v_fvarId_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; 
v___f_1095_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1095_, 0, v_fvarId_1085_);
v___x_1096_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1095_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object* v_fvarId_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(v_fvarId_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object* v_00_u03b1_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_1109_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(v_00_u03b1_1120_, v_msg_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg(){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object* v_00_u03b1_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object* v_00_u03b1_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(v_00_u03b1_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_ref_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_ref_1171_ = lean_ctor_get(v___y_1168_, 2);
v___x_1172_ = 0;
v___x_1173_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object* v___f_1185_, lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
lean_inc(v___y_1191_);
lean_inc_ref(v___y_1190_);
v___x_1199_ = lean_apply_9(v___f_1185_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, lean_box(0));
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_n(v_a_1200_, 2);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_1202_ = l_Lean_Name_mkStr4(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_a_1200_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
v___x_1204_ = l_Lean_Syntax_node1(v_a_1200_, v___x_1202_, v___x_1203_);
v___x_1205_ = l_Lean_Elab_Tactic_evalTactic(v___x_1204_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
lean_dec_ref(v___x_1186_);
v_a_1206_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1199_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1199_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object* v___f_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Elab_Tactic_evalRwa___lam__1(v___f_1214_, v___x_1215_, v___x_1216_, v___x_1217_, v_x_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRwa___closed__10(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Array_mkArray0___redArg();
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object* v_stx_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
lean_inc(v_stx_1267_);
v___x_1278_ = l_Lean_Syntax_isOfKind(v_stx_1267_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v_stx_1267_);
v___x_1279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = l_Lean_Syntax_getArg(v_stx_1267_, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1281_);
v___x_1283_ = l_Lean_Syntax_isOfKind(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v___x_1281_);
lean_dec(v_stx_1267_);
v___x_1284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1284_;
}
else
{
lean_object* v_ref_1285_; lean_object* v___f_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_ref_1285_ = lean_ctor_get(v_a_1274_, 2);
v___f_1286_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__4));
v___x_1287_ = 0;
v___x_1288_ = l_Lean_SourceInfo_fromRef(v_ref_1285_, v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__6));
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__7));
lean_inc_n(v___x_1288_, 3);
v___x_1291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1288_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1294_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1288_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_ctor_set(v___x_1295_, 2, v___x_1294_);
lean_inc_ref(v___x_1295_);
v___x_1296_ = l_Lean_Syntax_node1(v___x_1288_, v___x_1292_, v___x_1295_);
lean_inc(v___x_1281_);
v___x_1297_ = l_Lean_Syntax_node4(v___x_1288_, v___x_1289_, v___x_1291_, v___x_1296_, v___x_1281_, v___x_1295_);
v___x_1298_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_n(v_a_1299_, 4);
lean_dec_ref(v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
v___x_1302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_a_1299_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1303_, 0, v_a_1299_);
lean_ctor_set(v___x_1303_, 1, v___x_1293_);
lean_ctor_set(v___x_1303_, 2, v___x_1294_);
lean_inc_ref(v___x_1303_);
v___x_1304_ = l_Lean_Syntax_node1(v_a_1299_, v___x_1292_, v___x_1303_);
v___x_1305_ = l_Lean_Syntax_node4(v_a_1299_, v___x_1300_, v___x_1302_, v___x_1304_, v___x_1281_, v___x_1303_);
v___x_1306_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1306_, 0, v___x_1297_);
v___x_1307_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1267_, v___x_1306_, v___x_1305_, v___f_1286_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object* v_stx_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Elab_Tactic_evalRwa(v_stx_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1(){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1326_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1));
v___x_1329_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwa___boxed), 10, 0);
v___x_1330_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1326_, v___x_1327_, v___x_1328_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t v___x_1333_, lean_object* v_fvarId_1334_, uint8_t v_symm_1335_, lean_object* v_term_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1346_ = 2;
v___x_1347_ = lean_box(0);
v___x_1348_ = 0;
v___x_1349_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1346_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1 + 1, v___x_1333_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1 + 2, v___x_1348_);
v___x_1350_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_term_1336_, v_symm_1335_, v_fvarId_1334_, v___x_1349_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object* v___x_1351_, lean_object* v_fvarId_1352_, lean_object* v_symm_1353_, lean_object* v_term_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_2496__boxed_1364_; uint8_t v_symm_boxed_1365_; lean_object* v_res_1366_; 
v___x_2496__boxed_1364_ = lean_unbox(v___x_1351_);
v_symm_boxed_1365_ = lean_unbox(v_symm_1353_);
v_res_1366_ = l_Lean_Elab_Tactic_evalRwaAt___lam__0(v___x_2496__boxed_1364_, v_fvarId_1352_, v_symm_boxed_1365_, v_term_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object* v___x_1367_, lean_object* v_stx_1368_, lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v___f_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Elab_Tactic_getFVarId(v___x_1367_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_Syntax_getArg(v_stx_1368_, v___x_1369_);
v___x_1384_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v___x_1383_, v___x_1370_, v_a_1382_, v___f_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1384_;
}
else
{
lean_dec_ref(v___f_1371_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object* v___x_1385_, lean_object* v_stx_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v___f_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Elab_Tactic_evalRwaAt___lam__1(v___x_1385_, v_stx_1386_, v___x_1387_, v___x_1388_, v___f_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___x_1388_);
lean_dec(v___x_1387_);
lean_dec(v_stx_1386_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object* v_stx_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
lean_inc(v_stx_1420_);
v___x_1431_ = l_Lean_Syntax_isOfKind(v_stx_1420_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_stx_1420_);
v___x_1432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = l_Lean_Syntax_getArg(v_stx_1420_, v___x_1433_);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1434_);
v___x_1436_ = l_Lean_Syntax_isOfKind(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v___x_1434_);
lean_dec(v_stx_1420_);
v___x_1437_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1437_;
}
else
{
lean_object* v_ref_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___f_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_ref_1438_ = lean_ctor_get(v_a_1427_, 2);
v___x_1439_ = lean_box(v___x_1436_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_unsigned_to_nat(3u);
v___x_1443_ = l_Lean_Syntax_getArg(v_stx_1420_, v___x_1442_);
lean_inc(v___x_1434_);
lean_inc(v_stx_1420_);
lean_inc(v___x_1443_);
v___f_1444_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1444_, 0, v___x_1443_);
lean_closure_set(v___f_1444_, 1, v_stx_1420_);
lean_closure_set(v___f_1444_, 2, v___x_1441_);
lean_closure_set(v___f_1444_, 3, v___x_1434_);
lean_closure_set(v___f_1444_, 4, v___f_1440_);
v___x_1445_ = 0;
v___x_1446_ = l_Lean_SourceInfo_fromRef(v_ref_1438_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
lean_inc_n(v___x_1446_, 8);
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1446_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__9));
v___x_1451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__10, &l_Lean_Elab_Tactic_evalRwa___closed__10_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__10);
v___x_1453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1446_);
lean_ctor_set(v___x_1453_, 1, v___x_1451_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
v___x_1454_ = l_Lean_Syntax_node1(v___x_1446_, v___x_1450_, v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__3));
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__4));
v___x_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1446_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__6));
v___x_1459_ = l_Lean_Syntax_node1(v___x_1446_, v___x_1451_, v___x_1443_);
v___x_1460_ = l_Lean_Syntax_node1(v___x_1446_, v___x_1458_, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node2(v___x_1446_, v___x_1455_, v___x_1457_, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node1(v___x_1446_, v___x_1451_, v___x_1461_);
v___x_1463_ = l_Lean_Syntax_node4(v___x_1446_, v___x_1447_, v___x_1449_, v___x_1454_, v___x_1434_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__7));
v___x_1465_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1420_, v___f_1444_, v___x_1463_, v___x_1464_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object* v_stx_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Elab_Tactic_evalRwaAt(v_stx_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1(){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1485_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1));
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___boxed), 10, 0);
v___x_1488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1484_, v___x_1485_, v___x_1486_, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
return v_res_1490_;
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
