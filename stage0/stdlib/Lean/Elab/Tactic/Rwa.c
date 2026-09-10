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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSeq"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__5_value),LEAN_SCALAR_PTR_LITERAL(197, 231, 198, 107, 115, 169, 96, 174)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRwa___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRwa___closed__7;
static const lean_closure_object l_Lean_Elab_Tactic_evalRwa___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalRwa___lam__1___boxed, .m_arity = 14, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value)} };
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRwa___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRwa___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__9_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_evalRwa___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_evalRwa___closed__10_value;
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
uint8_t v_suppressElabErrors_boxed_135_; uint8_t v___y_5589__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_suppressElabErrors_boxed_135_ = lean_unbox(v_suppressElabErrors_132_);
v___y_5589__boxed_136_ = lean_unbox(v___y_133_);
v_res_137_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_135_, v___y_5589__boxed_136_, v_x_134_);
lean_dec(v_x_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_140_, lean_object* v_msgData_141_, uint8_t v_severity_142_, uint8_t v_isSilent_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___y_150_; lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; uint8_t v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; uint8_t v___y_190_; uint8_t v___y_191_; uint8_t v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_212_; lean_object* v___y_213_; uint8_t v___y_214_; uint8_t v___y_215_; uint8_t v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_229_; uint8_t v___x_234_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; uint8_t v___y_239_; uint8_t v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; uint8_t v___y_244_; uint8_t v___x_260_; 
v___x_234_ = 2;
v___x_260_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_234_);
if (v___x_260_ == 0)
{
v___y_244_ = v___x_260_;
goto v___jp_243_;
}
else
{
uint8_t v___x_261_; 
lean_inc_ref(v_msgData_141_);
v___x_261_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_141_);
v___y_244_ = v___x_261_;
goto v___jp_243_;
}
v___jp_149_:
{
lean_object* v___x_159_; lean_object* v_toCold_160_; lean_object* v_currNamespace_161_; lean_object* v_openDecls_162_; lean_object* v_env_163_; lean_object* v_nextMacroScope_164_; lean_object* v_ngen_165_; lean_object* v_auxDeclNGen_166_; lean_object* v_traceState_167_; lean_object* v_cache_168_; lean_object* v_messages_169_; lean_object* v_infoState_170_; lean_object* v_snapshotTasks_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_185_; 
v___x_159_ = lean_st_ref_take(v___y_158_);
v_toCold_160_ = lean_ctor_get(v___y_157_, 0);
v_currNamespace_161_ = lean_ctor_get(v_toCold_160_, 4);
v_openDecls_162_ = lean_ctor_get(v_toCold_160_, 5);
v_env_163_ = lean_ctor_get(v___x_159_, 0);
v_nextMacroScope_164_ = lean_ctor_get(v___x_159_, 1);
v_ngen_165_ = lean_ctor_get(v___x_159_, 2);
v_auxDeclNGen_166_ = lean_ctor_get(v___x_159_, 3);
v_traceState_167_ = lean_ctor_get(v___x_159_, 4);
v_cache_168_ = lean_ctor_get(v___x_159_, 5);
v_messages_169_ = lean_ctor_get(v___x_159_, 6);
v_infoState_170_ = lean_ctor_get(v___x_159_, 7);
v_snapshotTasks_171_ = lean_ctor_get(v___x_159_, 8);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_185_ == 0)
{
v___x_173_ = v___x_159_;
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_snapshotTasks_171_);
lean_inc(v_infoState_170_);
lean_inc(v_messages_169_);
lean_inc(v_cache_168_);
lean_inc(v_traceState_167_);
lean_inc(v_auxDeclNGen_166_);
lean_inc(v_ngen_165_);
lean_inc(v_nextMacroScope_164_);
lean_inc(v_env_163_);
lean_dec(v___x_159_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_openDecls_162_);
lean_inc(v_currNamespace_161_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_currNamespace_161_);
lean_ctor_set(v___x_175_, 1, v_openDecls_162_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___y_151_);
lean_inc_ref(v___y_156_);
lean_inc_ref(v___y_150_);
v___x_177_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_177_, 0, v___y_150_);
lean_ctor_set(v___x_177_, 1, v___y_153_);
lean_ctor_set(v___x_177_, 2, v___y_155_);
lean_ctor_set(v___x_177_, 3, v___y_156_);
lean_ctor_set(v___x_177_, 4, v___x_176_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5, v___y_152_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5 + 1, v___y_154_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5 + 2, v_isSilent_143_);
v___x_178_ = l_Lean_MessageLog_add(v___x_177_, v_messages_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 6, v___x_178_);
v___x_180_ = v___x_173_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_env_163_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_164_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v_cache_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v_infoState_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_snapshotTasks_171_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_st_ref_put(v___y_158_, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
v___jp_186_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v___x_195_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_141_);
v___x_196_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v___x_195_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_210_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc_ref_n(v___y_193_, 2);
v___x_201_ = l_Lean_FileMap_toPosition(v___y_193_, v___y_189_);
lean_dec(v___y_189_);
v___x_202_ = l_Lean_FileMap_toPosition(v___y_193_, v___y_194_);
lean_dec(v___y_194_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_191_ == 0)
{
lean_del_object(v___x_199_);
lean_dec_ref(v___y_187_);
v___y_150_ = v___y_188_;
v___y_151_ = v_a_197_;
v___y_152_ = v___y_190_;
v___y_153_ = v___x_201_;
v___y_154_ = v___y_192_;
v___y_155_ = v___x_203_;
v___y_156_ = v___x_204_;
v___y_157_ = v___y_146_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
else
{
uint8_t v___x_205_; 
lean_inc(v_a_197_);
v___x_205_ = l_Lean_MessageData_hasTag(v___y_187_, v_a_197_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec_ref_known(v___x_203_, 1);
lean_dec_ref(v___x_201_);
lean_dec(v_a_197_);
v___x_206_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_206_);
v___x_208_ = v___x_199_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
else
{
lean_del_object(v___x_199_);
v___y_150_ = v___y_188_;
v___y_151_ = v_a_197_;
v___y_152_ = v___y_190_;
v___y_153_ = v___x_201_;
v___y_154_ = v___y_192_;
v___y_155_ = v___x_203_;
v___y_156_ = v___x_204_;
v___y_157_ = v___y_146_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
}
}
}
v___jp_211_:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Syntax_getTailPos_x3f(v___y_218_, v___y_214_);
lean_dec(v___y_218_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_inc(v___y_219_);
v___y_187_ = v___y_212_;
v___y_188_ = v___y_213_;
v___y_189_ = v___y_219_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
v___y_193_ = v___y_217_;
v___y_194_ = v___y_219_;
goto v___jp_186_;
}
else
{
lean_object* v_val_221_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
v___y_187_ = v___y_212_;
v___y_188_ = v___y_213_;
v___y_189_ = v___y_219_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
v___y_193_ = v___y_217_;
v___y_194_ = v_val_221_;
goto v___jp_186_;
}
}
v___jp_222_:
{
lean_object* v_ref_230_; lean_object* v___x_231_; 
v_ref_230_ = l_Lean_replaceRef(v_ref_140_, v___y_227_);
v___x_231_ = l_Lean_Syntax_getPos_x3f(v_ref_230_, v___y_225_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
v___y_214_ = v___y_225_;
v___y_215_ = v___y_226_;
v___y_216_ = v___y_229_;
v___y_217_ = v___y_228_;
v___y_218_ = v_ref_230_;
v___y_219_ = v___x_232_;
goto v___jp_211_;
}
else
{
lean_object* v_val_233_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_231_, 1);
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
v___y_214_ = v___y_225_;
v___y_215_ = v___y_226_;
v___y_216_ = v___y_229_;
v___y_217_ = v___y_228_;
v___y_218_ = v_ref_230_;
v___y_219_ = v_val_233_;
goto v___jp_211_;
}
}
v___jp_235_:
{
if (v___y_242_ == 0)
{
v___y_223_ = v___y_236_;
v___y_224_ = v___y_237_;
v___y_225_ = v___y_239_;
v___y_226_ = v___y_240_;
v___y_227_ = v___y_241_;
v___y_228_ = v___y_238_;
v___y_229_ = v_severity_142_;
goto v___jp_222_;
}
else
{
v___y_223_ = v___y_236_;
v___y_224_ = v___y_237_;
v___y_225_ = v___y_239_;
v___y_226_ = v___y_240_;
v___y_227_ = v___y_241_;
v___y_228_ = v___y_238_;
v___y_229_ = v___x_234_;
goto v___jp_222_;
}
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
lean_object* v_toCold_245_; lean_object* v_ref_246_; uint8_t v_suppressElabErrors_247_; lean_object* v_fileName_248_; lean_object* v_fileMap_249_; lean_object* v_options_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___f_253_; uint8_t v___x_254_; uint8_t v___x_255_; 
v_toCold_245_ = lean_ctor_get(v___y_146_, 0);
v_ref_246_ = lean_ctor_get(v___y_146_, 2);
v_suppressElabErrors_247_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 1);
v_fileName_248_ = lean_ctor_get(v_toCold_245_, 0);
v_fileMap_249_ = lean_ctor_get(v_toCold_245_, 1);
v_options_250_ = lean_ctor_get(v_toCold_245_, 2);
v___x_251_ = lean_box(v_suppressElabErrors_247_);
v___x_252_ = lean_box(v___y_244_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_253_, 0, v___x_251_);
lean_closure_set(v___f_253_, 1, v___x_252_);
v___x_254_ = 1;
v___x_255_ = l_Lean_instBEqMessageSeverity_beq(v_severity_142_, v___x_254_);
if (v___x_255_ == 0)
{
v___y_236_ = v___f_253_;
v___y_237_ = v_fileName_248_;
v___y_238_ = v_fileMap_249_;
v___y_239_ = v___y_244_;
v___y_240_ = v_suppressElabErrors_247_;
v___y_241_ = v_ref_246_;
v___y_242_ = v___x_255_;
goto v___jp_235_;
}
else
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = l_Lean_warningAsError;
v___x_257_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v_options_250_, v___x_256_);
v___y_236_ = v___f_253_;
v___y_237_ = v_fileName_248_;
v___y_238_ = v_fileMap_249_;
v___y_239_ = v___y_244_;
v___y_240_ = v_suppressElabErrors_247_;
v___y_241_ = v_ref_246_;
v___y_242_ = v___x_257_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v_msgData_141_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_262_, lean_object* v_msgData_263_, lean_object* v_severity_264_, lean_object* v_isSilent_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v_severity_boxed_271_; uint8_t v_isSilent_boxed_272_; lean_object* v_res_273_; 
v_severity_boxed_271_ = lean_unbox(v_severity_264_);
v_isSilent_boxed_272_ = lean_unbox(v_isSilent_265_);
v_res_273_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_262_, v_msgData_263_, v_severity_boxed_271_, v_isSilent_boxed_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v_ref_262_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object* v_ref_274_, lean_object* v_msgData_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
uint8_t v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 1;
v___x_286_ = 0;
v___x_287_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_274_, v_msgData_275_, v___x_285_, v___x_286_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object* v_ref_288_, lean_object* v_msgData_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_ref_288_, v_msgData_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v_ref_288_);
return v_res_299_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object* v_linterOption_306_, lean_object* v_stx_307_, lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_name_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_336_; 
v_name_318_ = lean_ctor_get(v_linterOption_306_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_linterOption_306_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_linterOption_306_, 1);
lean_dec(v_unused_337_);
v___x_320_ = v_linterOption_306_;
v_isShared_321_ = v_isSharedCheck_336_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_name_318_);
lean_dec(v_linterOption_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_336_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1);
lean_inc(v_name_318_);
v___x_323_ = l_Lean_MessageData_ofName(v_name_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 7);
lean_ctor_set(v___x_320_, 1, v___x_323_);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_335_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_disable_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v_disable_328_ = l_Lean_MessageData_note(v___x_327_);
v___x_329_ = l_Lean_Linter_linterMessageTag;
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v_msg_308_);
lean_ctor_set(v___x_330_, 1, v_disable_328_);
v___x_331_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_332_, 0, v_name_318_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_inc(v_stx_307_);
v___x_333_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_333_, 0, v_stx_307_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_stx_307_, v___x_333_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v_stx_307_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object* v_linterOption_338_, lean_object* v_stx_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v_linterOption_338_, v_stx_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object* v_o_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v_env_355_; lean_object* v___x_356_; lean_object* v_toEnvExtension_357_; lean_object* v_asyncMode_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_merged_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v___x_354_ = lean_st_ref_get(v___y_352_);
v_env_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_ref(v_env_355_);
lean_dec(v___x_354_);
v___x_356_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_357_ = lean_ctor_get(v___x_356_, 0);
v_asyncMode_358_ = lean_ctor_get(v_toEnvExtension_357_, 2);
v___x_359_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_360_ = lean_box(0);
v___x_361_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_359_, v___x_356_, v_env_355_, v_asyncMode_358_, v___x_360_);
v_merged_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_361_, 1);
lean_dec(v_unused_371_);
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_merged_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_merged_362_);
lean_ctor_set(v___x_364_, 0, v_o_351_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_o_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_merged_362_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg___boxed(lean_object* v_o_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_372_, v___y_373_);
lean_dec(v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_toCold_385_; lean_object* v_options_386_; lean_object* v___x_387_; 
v_toCold_385_ = lean_ctor_get(v___y_382_, 0);
v_options_386_ = lean_ctor_get(v_toCold_385_, 2);
lean_inc_ref(v_options_386_);
v___x_387_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_options_386_, v___y_383_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0___boxed(lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_397_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__0));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__5));
v___x_408_ = l_Lean_MessageData_ofFormat(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(lean_object* v_initialState_409_, lean_object* v_ref_410_, lean_object* v_replacement_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_469_; 
v___x_421_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0(v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_469_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_469_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_469_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = l_Lean_Elab_Tactic_linter_unnecessaryRwa;
v___x_427_ = l_Lean_Linter_getLinterValue(v___x_426_, v_a_422_);
lean_dec(v_a_422_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec(v_replacement_411_);
lean_dec(v_ref_410_);
lean_dec_ref(v_initialState_409_);
v___x_428_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_428_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_del_object(v___x_424_);
v___x_432_ = lean_box(0);
lean_inc(v_replacement_411_);
v___x_433_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_409_, v_replacement_411_, v___x_432_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1);
v___x_436_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_dec(v_replacement_411_);
v___x_437_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_426_, v_ref_410_, v___x_435_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__3));
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_replacement_411_);
v___x_440_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_432_);
lean_ctor_set(v___x_440_, 2, v___x_432_);
lean_ctor_set(v___x_440_, 3, v___x_432_);
lean_ctor_set(v___x_440_, 4, v___x_432_);
lean_ctor_set(v___x_440_, 5, v___x_432_);
lean_inc(v_ref_410_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_ref_410_);
v___x_442_ = 4;
lean_inc_ref(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_443_, 0, v___x_440_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_432_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3, v___x_442_);
v___x_444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_array_push(v___x_446_, v___x_443_);
v___x_448_ = 0;
v___x_449_ = l_Lean_MessageData_hint(v___x_444_, v___x_447_, v___x_441_, v___x_432_, v___x_448_, v_a_418_, v_a_419_);
lean_dec_ref(v___x_447_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_435_);
lean_ctor_set(v___x_451_, 1, v_a_450_);
v___x_452_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_426_, v_ref_410_, v___x_451_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_452_;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_ref_410_);
v_a_453_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_449_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_replacement_411_);
lean_dec(v_ref_410_);
v_a_461_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_433_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_433_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___boxed(lean_object* v_initialState_470_, lean_object* v_ref_471_, lean_object* v_replacement_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_initialState_470_, v_ref_471_, v_replacement_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(lean_object* v_o_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_o_483_, v___y_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___boxed(lean_object* v_o_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0(v_o_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(lean_object* v_ref_505_, lean_object* v_msgData_506_, uint8_t v_severity_507_, uint8_t v_isSilent_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_505_, v_msgData_506_, v_severity_507_, v_isSilent_508_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_519_, lean_object* v_msgData_520_, lean_object* v_severity_521_, lean_object* v_isSilent_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_severity_boxed_532_; uint8_t v_isSilent_boxed_533_; lean_object* v_res_534_; 
v_severity_boxed_532_ = lean_unbox(v_severity_521_);
v_isSilent_boxed_533_ = lean_unbox(v_isSilent_522_);
v_res_534_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3(v_ref_519_, v_msgData_520_, v_severity_boxed_532_, v_isSilent_boxed_533_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v_ref_519_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_ref_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_ref_574_ = lean_ctor_get(v___y_571_, 2);
v___x_575_ = 0;
v___x_576_ = l_Lean_SourceInfo_fromRef(v_ref_574_, v___x_575_);
v___x_577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
lean_inc_n(v___x_576_, 6);
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_576_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_Syntax_node1(v___x_576_, v___x_583_, v___x_585_);
v___x_587_ = l_Lean_Syntax_node1(v___x_576_, v___x_582_, v___x_586_);
v___x_588_ = l_Lean_Syntax_node1(v___x_576_, v___x_581_, v___x_587_);
v___x_589_ = l_Lean_Syntax_node1(v___x_576_, v___x_580_, v___x_588_);
v___x_590_ = l_Lean_Syntax_node2(v___x_576_, v___x_577_, v___x_579_, v___x_589_);
v___x_591_ = l_Lean_Elab_Tactic_evalTactic(v___x_590_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_601_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = 1;
v___x_596_ = lean_box(v___x_595_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_591_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_591_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___boxed(lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0(v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(lean_object* v___f_620_, lean_object* v_close_621_, lean_object* v_a_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_624_, v___y_626_, v___y_628_, v___y_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_620_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec(v_a_633_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_close_621_);
return v___x_634_;
}
else
{
lean_object* v_a_635_; uint8_t v___y_637_; uint8_t v___x_665_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
v___x_665_ = l_Lean_Exception_isInterrupt(v_a_635_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_Exception_isRuntime(v_a_635_);
v___y_637_ = v___x_666_;
goto v___jp_636_;
}
else
{
lean_dec(v_a_635_);
v___y_637_ = v___x_665_;
goto v___jp_636_;
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref_known(v___x_634_, 1);
v___x_638_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_633_, v___y_637_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v___x_639_; 
lean_dec_ref_known(v___x_638_, 1);
v___x_639_ = lean_apply_10(v_close_621_, v_a_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_648_);
v___x_641_ = v___x_639_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_dec(v___x_639_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_box(v___y_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_649_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_639_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_639_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
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
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_close_621_);
v_a_657_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_638_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_638_);
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
else
{
lean_dec(v_a_633_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_close_621_);
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_close_621_);
lean_dec_ref(v___f_620_);
v_a_667_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_632_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_632_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed(lean_object* v___f_675_, lean_object* v_close_676_, lean_object* v_a_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1(v___f_675_, v_close_676_, v_a_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(lean_object* v_rewrite_725_, lean_object* v___f_726_, lean_object* v_close_727_, lean_object* v_ref_728_, lean_object* v_replacement_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___x_810_; 
v___x_810_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_731_, v___y_733_, v___y_735_, v___y_737_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
v___x_812_ = lean_apply_9(v_rewrite_725_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___f_814_; lean_object* v___x_815_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___f_814_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_814_, 0, v___f_726_);
lean_closure_set(v___f_814_, 1, v_close_727_);
lean_closure_set(v___f_814_, 2, v_a_813_);
v___x_815_ = l_Lean_Elab_Tactic_focus___redArg(v___f_814_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_817_) == 0)
{
uint8_t v___x_818_; 
v___x_818_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
if (v___x_818_ == 0)
{
lean_dec_ref_known(v___x_817_, 1);
lean_dec(v_a_811_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
v___y_740_ = v___y_730_;
v___y_741_ = v___y_731_;
v___y_742_ = v___y_732_;
v___y_743_ = v___y_733_;
v___y_744_ = v___y_734_;
v___y_745_ = v___y_735_;
v___y_746_ = v___y_736_;
v___y_747_ = v___y_737_;
goto v___jp_739_;
}
else
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_817_, 1);
v___x_820_ = l_List_isEmpty___redArg(v_a_819_);
lean_dec(v_a_819_);
if (v___x_820_ == 0)
{
lean_dec(v_a_811_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
v___y_740_ = v___y_730_;
v___y_741_ = v___y_731_;
v___y_742_ = v___y_732_;
v___y_743_ = v___y_733_;
v___y_744_ = v___y_734_;
v___y_745_ = v___y_735_;
v___y_746_ = v___y_736_;
v___y_747_ = v___y_737_;
goto v___jp_739_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_a_811_, v_ref_728_, v_replacement_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref_known(v___x_821_, 1);
v___y_740_ = v___y_730_;
v___y_741_ = v___y_731_;
v___y_742_ = v___y_732_;
v___y_743_ = v___y_733_;
v___y_744_ = v___y_734_;
v___y_745_ = v___y_735_;
v___y_746_ = v___y_736_;
v___y_747_ = v___y_737_;
goto v___jp_739_;
}
else
{
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_816_);
lean_dec(v_a_811_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
v_a_822_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_817_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_817_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_a_811_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
v_a_830_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_815_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_815_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v_a_811_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
lean_dec_ref(v_close_727_);
lean_dec_ref(v___f_726_);
v_a_838_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_812_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_812_);
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
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_replacement_729_);
lean_dec(v_ref_728_);
lean_dec_ref(v_close_727_);
lean_dec_ref(v___f_726_);
lean_dec_ref(v_rewrite_725_);
v_a_846_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_810_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_810_);
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
v___jp_739_:
{
lean_object* v_ref_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_ref_748_ = lean_ctor_get(v___y_746_, 2);
v___x_749_ = 0;
v___x_750_ = l_Lean_SourceInfo_fromRef(v_ref_748_, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1));
v___x_752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2));
lean_inc_n(v___x_750_, 37);
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4));
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_750_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6));
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_750_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_750_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_750_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_750_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_750_, v___x_769_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node2(v___x_750_, v___x_766_, v___x_768_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_778_);
lean_inc_ref_n(v___x_765_, 2);
v___x_780_ = l_Lean_Syntax_node2(v___x_750_, v___x_763_, v___x_765_, v___x_779_);
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_750_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
v___x_784_ = l_Lean_Syntax_node1(v___x_750_, v___x_782_, v___x_783_);
v___x_785_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node2(v___x_750_, v___x_763_, v___x_765_, v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13));
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14));
v___x_791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_750_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
v___x_792_ = l_Lean_Syntax_node1(v___x_750_, v___x_790_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node2(v___x_750_, v___x_763_, v___x_765_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node3(v___x_750_, v___x_756_, v___x_780_, v___x_788_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v___x_750_, v___x_761_, v___x_762_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_798_);
v___x_800_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_750_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_Syntax_node3(v___x_750_, v___x_757_, v___x_759_, v___x_801_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node1(v___x_750_, v___x_756_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node1(v___x_750_, v___x_755_, v___x_805_);
v___x_807_ = l_Lean_Syntax_node1(v___x_750_, v___x_754_, v___x_806_);
v___x_808_ = l_Lean_Syntax_node2(v___x_750_, v___x_751_, v___x_753_, v___x_807_);
v___x_809_ = l_Lean_Elab_Tactic_evalTactic(v___x_808_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object* v_rewrite_854_, lean_object* v___f_855_, lean_object* v_close_856_, lean_object* v_ref_857_, lean_object* v_replacement_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(v_rewrite_854_, v___f_855_, v_close_856_, v_ref_857_, v_replacement_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object* v_ref_870_, lean_object* v_rewrite_871_, lean_object* v_replacement_872_, lean_object* v_close_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_885_; 
v___f_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0));
v___f_884_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed), 14, 5);
lean_closure_set(v___f_884_, 0, v_rewrite_871_);
lean_closure_set(v___f_884_, 1, v___f_883_);
lean_closure_set(v___f_884_, 2, v_close_873_);
lean_closure_set(v___f_884_, 3, v_ref_870_);
lean_closure_set(v___f_884_, 4, v_replacement_872_);
v___x_885_ = l_Lean_Elab_Tactic_focus___redArg(v___f_884_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object* v_ref_886_, lean_object* v_rewrite_887_, lean_object* v_replacement_888_, lean_object* v_close_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_886_, v_rewrite_887_, v_replacement_888_, v_close_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object* v_00_u03b1_900_, lean_object* v_ref_901_, lean_object* v_rewrite_902_, lean_object* v_replacement_903_, lean_object* v_close_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_901_, v_rewrite_902_, v_replacement_903_, v_close_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object* v_00_u03b1_915_, lean_object* v_ref_916_, lean_object* v_rewrite_917_, lean_object* v_replacement_918_, lean_object* v_close_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(v_00_u03b1_915_, v_ref_916_, v_rewrite_917_, v_replacement_918_, v_close_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object* v_msg_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_ref_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_ref_936_ = lean_ctor_get(v___y_933_, 2);
v___x_937_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msg_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_946_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
lean_inc(v_ref_936_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_ref_936_);
lean_ctor_set(v___x_942_, 1, v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_953_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object* v_fvarId_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_967_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___x_989_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_mkFVar(v_fvarId_965_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc_ref(v___x_977_);
v___x_989_ = lean_infer_type(v___x_977_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_MVarId_getType(v_a_976_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; uint8_t v_a_994_; lean_object* v___x_1014_; uint8_t v_foApprox_1015_; uint8_t v_ctxApprox_1016_; uint8_t v_quasiPatternApprox_1017_; uint8_t v_constApprox_1018_; uint8_t v_isDefEqStuckEx_1019_; uint8_t v_unificationHints_1020_; uint8_t v_proofIrrelevance_1021_; uint8_t v_offsetCnstrs_1022_; uint8_t v_transparency_1023_; uint8_t v_etaStruct_1024_; uint8_t v_univApprox_1025_; uint8_t v_iota_1026_; uint8_t v_beta_1027_; uint8_t v_proj_1028_; uint8_t v_zeta_1029_; uint8_t v_zetaDelta_1030_; uint8_t v_zetaUnused_1031_; uint8_t v_zetaHave_1032_; uint8_t v_canUnfoldPredicateConfig_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1067_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_1014_ = l_Lean_Meta_Context_config(v___y_970_);
v_foApprox_1015_ = lean_ctor_get_uint8(v___x_1014_, 0);
v_ctxApprox_1016_ = lean_ctor_get_uint8(v___x_1014_, 1);
v_quasiPatternApprox_1017_ = lean_ctor_get_uint8(v___x_1014_, 2);
v_constApprox_1018_ = lean_ctor_get_uint8(v___x_1014_, 3);
v_isDefEqStuckEx_1019_ = lean_ctor_get_uint8(v___x_1014_, 4);
v_unificationHints_1020_ = lean_ctor_get_uint8(v___x_1014_, 5);
v_proofIrrelevance_1021_ = lean_ctor_get_uint8(v___x_1014_, 6);
v_offsetCnstrs_1022_ = lean_ctor_get_uint8(v___x_1014_, 8);
v_transparency_1023_ = lean_ctor_get_uint8(v___x_1014_, 9);
v_etaStruct_1024_ = lean_ctor_get_uint8(v___x_1014_, 10);
v_univApprox_1025_ = lean_ctor_get_uint8(v___x_1014_, 11);
v_iota_1026_ = lean_ctor_get_uint8(v___x_1014_, 12);
v_beta_1027_ = lean_ctor_get_uint8(v___x_1014_, 13);
v_proj_1028_ = lean_ctor_get_uint8(v___x_1014_, 14);
v_zeta_1029_ = lean_ctor_get_uint8(v___x_1014_, 15);
v_zetaDelta_1030_ = lean_ctor_get_uint8(v___x_1014_, 16);
v_zetaUnused_1031_ = lean_ctor_get_uint8(v___x_1014_, 17);
v_zetaHave_1032_ = lean_ctor_get_uint8(v___x_1014_, 18);
v_canUnfoldPredicateConfig_1033_ = lean_ctor_get_uint8(v___x_1014_, 19);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1035_ = v___x_1014_;
v_isShared_1036_ = v_isSharedCheck_1067_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v___x_1014_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1067_;
goto v_resetjp_1034_;
}
v___jp_993_:
{
if (v_a_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2));
v___x_997_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_990_, v_a_992_, v___x_995_, v___x_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4);
v___x_1000_ = l_Lean_indentExpr(v___x_977_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_998_);
v___x_1005_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v___x_1004_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___x_977_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
v_a_1006_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_997_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_997_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_dec(v_a_992_);
lean_dec(v_a_990_);
v___y_979_ = v___y_967_;
v___y_980_ = v___y_968_;
v___y_981_ = v___y_969_;
v___y_982_ = v___y_970_;
v___y_983_ = v___y_971_;
v___y_984_ = v___y_972_;
v___y_985_ = v___y_973_;
goto v___jp_978_;
}
}
v_resetjp_1034_:
{
uint8_t v_trackZetaDelta_1037_; lean_object* v_zetaDeltaSet_1038_; lean_object* v_lctx_1039_; lean_object* v_localInstances_1040_; lean_object* v_defEqCtx_x3f_1041_; lean_object* v_synthPendingDepth_1042_; lean_object* v_customCanUnfoldPredicate_x3f_1043_; uint8_t v_univApprox_1044_; uint8_t v_inTypeClassResolution_1045_; uint8_t v_cacheInferType_1046_; uint8_t v___x_1047_; lean_object* v___x_1049_; 
v_trackZetaDelta_1037_ = lean_ctor_get_uint8(v___y_970_, sizeof(void*)*7);
v_zetaDeltaSet_1038_ = lean_ctor_get(v___y_970_, 1);
v_lctx_1039_ = lean_ctor_get(v___y_970_, 2);
v_localInstances_1040_ = lean_ctor_get(v___y_970_, 3);
v_defEqCtx_x3f_1041_ = lean_ctor_get(v___y_970_, 4);
v_synthPendingDepth_1042_ = lean_ctor_get(v___y_970_, 5);
v_customCanUnfoldPredicate_x3f_1043_ = lean_ctor_get(v___y_970_, 6);
v_univApprox_1044_ = lean_ctor_get_uint8(v___y_970_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1045_ = lean_ctor_get_uint8(v___y_970_, sizeof(void*)*7 + 2);
v_cacheInferType_1046_ = lean_ctor_get_uint8(v___y_970_, sizeof(void*)*7 + 3);
v___x_1047_ = 1;
if (v_isShared_1036_ == 0)
{
v___x_1049_ = v___x_1035_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 0, v_foApprox_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 1, v_ctxApprox_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 2, v_quasiPatternApprox_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 3, v_constApprox_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 4, v_isDefEqStuckEx_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 5, v_unificationHints_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 6, v_proofIrrelevance_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 8, v_offsetCnstrs_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 9, v_transparency_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 10, v_etaStruct_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 11, v_univApprox_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 12, v_iota_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 13, v_beta_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 14, v_proj_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 15, v_zeta_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 16, v_zetaDelta_1030_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 17, v_zetaUnused_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 18, v_zetaHave_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 19, v_canUnfoldPredicateConfig_1033_);
v___x_1049_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
uint64_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_ctor_set_uint8(v___x_1049_, 7, v___x_1047_);
v___x_1050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set_uint64(v___x_1051_, sizeof(void*)*1, v___x_1050_);
lean_inc(v_customCanUnfoldPredicate_x3f_1043_);
lean_inc(v_synthPendingDepth_1042_);
lean_inc(v_defEqCtx_x3f_1041_);
lean_inc_ref(v_localInstances_1040_);
lean_inc_ref(v_lctx_1039_);
lean_inc(v_zetaDeltaSet_1038_);
v___x_1052_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_zetaDeltaSet_1038_);
lean_ctor_set(v___x_1052_, 2, v_lctx_1039_);
lean_ctor_set(v___x_1052_, 3, v_localInstances_1040_);
lean_ctor_set(v___x_1052_, 4, v_defEqCtx_x3f_1041_);
lean_ctor_set(v___x_1052_, 5, v_synthPendingDepth_1042_);
lean_ctor_set(v___x_1052_, 6, v_customCanUnfoldPredicate_x3f_1043_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7, v_trackZetaDelta_1037_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 1, v_univApprox_1044_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1045_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*7 + 3, v_cacheInferType_1046_);
lean_inc(v_a_992_);
lean_inc(v_a_990_);
v___x_1053_ = l_Lean_Meta_isExprDefEq(v_a_990_, v_a_992_, v___x_1052_, v___y_971_, v___y_972_, v___y_973_);
lean_dec_ref_known(v___x_1052_, 7);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; uint8_t v___x_1055_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = lean_unbox(v_a_1054_);
lean_dec(v_a_1054_);
v_a_994_ = v___x_1055_;
goto v___jp_993_;
}
else
{
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1056_; uint8_t v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1057_ = lean_unbox(v_a_1056_);
lean_dec(v_a_1056_);
v_a_994_ = v___x_1057_;
goto v___jp_993_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_a_992_);
lean_dec(v_a_990_);
lean_dec_ref(v___x_977_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
v_a_1058_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1053_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1053_);
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
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_990_);
lean_dec_ref(v___x_977_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
v_a_1068_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_991_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_991_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v___x_977_);
lean_dec(v_a_976_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
v_a_1076_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_989_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_989_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
v___jp_978_:
{
lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1));
v___x_987_ = 1;
v___x_988_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_986_, v___x_977_, v___x_987_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v___x_988_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_fvarId_965_);
v_a_1084_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_975_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_975_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object* v_fvarId_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(v_fvarId_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object* v_fvarId_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_1114_; 
v___f_1113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1113_, 0, v_fvarId_1103_);
v___x_1114_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1113_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object* v_fvarId_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(v_fvarId_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object* v_00_u03b1_1126_, lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_1127_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(v_00_u03b1_1138_, v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v___x_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg(){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object* v_00_u03b1_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object* v_00_u03b1_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(v_00_u03b1_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_ref_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_ref_1189_ = lean_ctor_get(v___y_1186_, 2);
v___x_1190_ = 0;
v___x_1191_ = l_Lean_SourceInfo_fromRef(v_ref_1189_, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object* v___f_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
v___x_1217_ = lean_apply_9(v___f_1203_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, lean_box(0));
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_n(v_a_1218_, 2);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_1220_ = l_Lean_Name_mkStr4(v___x_1204_, v___x_1205_, v___x_1206_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1218_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
v___x_1222_ = l_Lean_Syntax_node1(v_a_1218_, v___x_1220_, v___x_1221_);
v___x_1223_ = l_Lean_Elab_Tactic_evalTactic(v___x_1222_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1223_;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1204_);
v_a_1224_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1217_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1217_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object* v___f_1232_, lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v___x_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Elab_Tactic_evalRwa___lam__1(v___f_1232_, v___x_1233_, v___x_1234_, v___x_1235_, v_x_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRwa___closed__7(void){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Array_mkArray0(lean_box(0));
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object* v_stx_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
lean_inc(v_stx_1285_);
v___x_1296_ = l_Lean_Syntax_isOfKind(v_stx_1285_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_dec(v_stx_1285_);
v___x_1297_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = l_Lean_Syntax_getArg(v_stx_1285_, v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1299_);
v___x_1301_ = l_Lean_Syntax_isOfKind(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v___x_1299_);
lean_dec(v_stx_1285_);
v___x_1302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1302_;
}
else
{
lean_object* v_ref_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_ref_1303_ = lean_ctor_get(v_a_1292_, 2);
v___x_1304_ = 0;
v___x_1305_ = l_Lean_SourceInfo_fromRef(v_ref_1303_, v___x_1304_);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__4));
lean_inc_n(v___x_1305_, 3);
v___x_1307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_n(v_a_1309_, 4);
lean_dec_ref(v___x_1308_);
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__6));
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1312_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__7, &l_Lean_Elab_Tactic_evalRwa___closed__7_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__7);
v___x_1313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1305_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
v___f_1314_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__8));
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__10));
lean_inc_ref(v___x_1313_);
v___x_1316_ = l_Lean_Syntax_node1(v___x_1305_, v___x_1315_, v___x_1313_);
lean_inc(v___x_1299_);
v___x_1317_ = l_Lean_Syntax_node4(v___x_1305_, v___x_1310_, v___x_1307_, v___x_1316_, v___x_1299_, v___x_1313_);
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
v___x_1320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1309_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1309_);
lean_ctor_set(v___x_1321_, 1, v___x_1311_);
lean_ctor_set(v___x_1321_, 2, v___x_1312_);
lean_inc_ref(v___x_1321_);
v___x_1322_ = l_Lean_Syntax_node1(v_a_1309_, v___x_1315_, v___x_1321_);
v___x_1323_ = l_Lean_Syntax_node4(v_a_1309_, v___x_1318_, v___x_1320_, v___x_1322_, v___x_1299_, v___x_1321_);
v___x_1324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1324_, 0, v___x_1317_);
v___x_1325_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1285_, v___x_1324_, v___x_1323_, v___f_1314_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object* v_stx_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Elab_Tactic_evalRwa(v_stx_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1344_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
v___x_1346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1));
v___x_1347_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwa___boxed), 10, 0);
v___x_1348_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t v___x_1351_, lean_object* v_fvarId_1352_, uint8_t v_symm_1353_, lean_object* v_term_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1364_ = 2;
v___x_1365_ = lean_box(0);
v___x_1366_ = 0;
v___x_1367_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*1, v___x_1364_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*1 + 1, v___x_1351_);
lean_ctor_set_uint8(v___x_1367_, sizeof(void*)*1 + 2, v___x_1366_);
v___x_1368_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_term_1354_, v_symm_1353_, v_fvarId_1352_, v___x_1367_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object* v___x_1369_, lean_object* v_fvarId_1370_, lean_object* v_symm_1371_, lean_object* v_term_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v___x_2487__boxed_1382_; uint8_t v_symm_boxed_1383_; lean_object* v_res_1384_; 
v___x_2487__boxed_1382_ = lean_unbox(v___x_1369_);
v_symm_boxed_1383_ = lean_unbox(v_symm_1371_);
v_res_1384_ = l_Lean_Elab_Tactic_evalRwaAt___lam__0(v___x_2487__boxed_1382_, v_fvarId_1370_, v_symm_boxed_1383_, v_term_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object* v___x_1385_, lean_object* v_stx_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v___f_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Elab_Tactic_getFVarId(v___x_1385_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = l_Lean_Syntax_getArg(v_stx_1386_, v___x_1387_);
v___x_1402_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v___x_1401_, v___x_1388_, v_a_1400_, v___f_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1402_;
}
else
{
lean_dec_ref(v___f_1389_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object* v___x_1403_, lean_object* v_stx_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___f_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Elab_Tactic_evalRwaAt___lam__1(v___x_1403_, v_stx_1404_, v___x_1405_, v___x_1406_, v___f_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___x_1406_);
lean_dec(v___x_1405_);
lean_dec(v_stx_1404_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object* v_stx_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
lean_inc(v_stx_1438_);
v___x_1449_ = l_Lean_Syntax_isOfKind(v_stx_1438_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v_stx_1438_);
v___x_1450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = l_Lean_Syntax_getArg(v_stx_1438_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1452_);
v___x_1454_ = l_Lean_Syntax_isOfKind(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec(v___x_1452_);
lean_dec(v_stx_1438_);
v___x_1455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1455_;
}
else
{
lean_object* v_ref_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_ref_1456_ = lean_ctor_get(v_a_1445_, 2);
v___x_1457_ = lean_box(v___x_1454_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1458_, 0, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_unsigned_to_nat(3u);
v___x_1461_ = l_Lean_Syntax_getArg(v_stx_1438_, v___x_1460_);
lean_inc(v___x_1452_);
lean_inc(v_stx_1438_);
lean_inc(v___x_1461_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1462_, 0, v___x_1461_);
lean_closure_set(v___f_1462_, 1, v_stx_1438_);
lean_closure_set(v___f_1462_, 2, v___x_1459_);
lean_closure_set(v___f_1462_, 3, v___x_1452_);
lean_closure_set(v___f_1462_, 4, v___f_1458_);
v___x_1463_ = 0;
v___x_1464_ = l_Lean_SourceInfo_fromRef(v_ref_1456_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
lean_inc_n(v___x_1464_, 8);
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1464_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__10));
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1470_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__7, &l_Lean_Elab_Tactic_evalRwa___closed__7_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__7);
v___x_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1464_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node1(v___x_1464_, v___x_1468_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__3));
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__4));
v___x_1475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1464_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__6));
v___x_1477_ = l_Lean_Syntax_node1(v___x_1464_, v___x_1469_, v___x_1461_);
v___x_1478_ = l_Lean_Syntax_node1(v___x_1464_, v___x_1476_, v___x_1477_);
v___x_1479_ = l_Lean_Syntax_node2(v___x_1464_, v___x_1473_, v___x_1475_, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node1(v___x_1464_, v___x_1469_, v___x_1479_);
v___x_1481_ = l_Lean_Syntax_node4(v___x_1464_, v___x_1465_, v___x_1467_, v___x_1472_, v___x_1452_, v___x_1480_);
v___x_1482_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__7));
v___x_1483_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1438_, v___f_1462_, v___x_1481_, v___x_1482_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object* v_stx_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Elab_Tactic_evalRwaAt(v_stx_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1(){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1));
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___boxed), 10, 0);
v___x_1506_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1502_, v___x_1503_, v___x_1504_, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
return v_res_1508_;
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
