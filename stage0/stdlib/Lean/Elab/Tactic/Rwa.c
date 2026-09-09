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
lean_object* v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_mctx_84_; lean_object* v_lctx_85_; lean_object* v_options_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_env_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_env_82_);
lean_dec(v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_77_);
v_mctx_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_84_);
lean_dec(v___x_83_);
v_lctx_85_ = lean_ctor_get(v___y_76_, 2);
v_options_86_ = lean_ctor_get(v___y_78_, 1);
lean_inc_ref(v_options_86_);
lean_inc_ref(v_lctx_85_);
v___x_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_87_, 0, v_env_82_);
lean_ctor_set(v___x_87_, 1, v_mctx_84_);
lean_ctor_set(v___x_87_, 2, v_lctx_85_);
lean_ctor_set(v___x_87_, 3, v_options_86_);
v___x_88_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_msgData_75_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msgData_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_103_, uint8_t v___y_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 1)
{
lean_object* v_pre_106_; 
v_pre_106_ = lean_ctor_get(v_x_105_, 0);
switch(lean_obj_tag(v_pre_106_))
{
case 1:
{
lean_object* v_pre_107_; 
v_pre_107_ = lean_ctor_get(v_pre_106_, 0);
switch(lean_obj_tag(v_pre_107_))
{
case 0:
{
lean_object* v_str_108_; lean_object* v_str_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_str_108_ = lean_ctor_get(v_x_105_, 1);
v_str_109_ = lean_ctor_get(v_pre_106_, 1);
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_111_ = lean_string_dec_eq(v_str_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Rwa_1572114636____hygCtx___hyg_4_));
v___x_113_ = lean_string_dec_eq(v_str_109_, v___x_112_);
if (v___x_113_ == 0)
{
return v___x_113_;
}
else
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_115_ = lean_string_dec_eq(v_str_108_, v___x_114_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
return v_suppressElabErrors_103_;
}
}
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_117_ = lean_string_dec_eq(v_str_108_, v___x_116_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
return v_suppressElabErrors_103_;
}
}
}
case 1:
{
lean_object* v_pre_118_; 
v_pre_118_ = lean_ctor_get(v_pre_107_, 0);
if (lean_obj_tag(v_pre_118_) == 0)
{
lean_object* v_str_119_; lean_object* v_str_120_; lean_object* v_str_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_str_119_ = lean_ctor_get(v_x_105_, 1);
v_str_120_ = lean_ctor_get(v_pre_106_, 1);
v_str_121_ = lean_ctor_get(v_pre_107_, 1);
v___x_122_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_123_ = lean_string_dec_eq(v_str_121_, v___x_122_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_125_ = lean_string_dec_eq(v_str_120_, v___x_124_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_127_ = lean_string_dec_eq(v_str_119_, v___x_126_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
return v_suppressElabErrors_103_;
}
}
}
}
else
{
return v___y_104_;
}
}
default: 
{
return v___y_104_;
}
}
}
case 0:
{
lean_object* v_str_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_str_128_ = lean_ctor_get(v_x_105_, 1);
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_130_ = lean_string_dec_eq(v_str_128_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
return v_suppressElabErrors_103_;
}
}
default: 
{
return v___y_104_;
}
}
}
else
{
return v___y_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_131_, lean_object* v___y_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_suppressElabErrors_boxed_134_; uint8_t v___y_5551__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_suppressElabErrors_boxed_134_ = lean_unbox(v_suppressElabErrors_131_);
v___y_5551__boxed_135_ = lean_unbox(v___y_132_);
v_res_136_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_134_, v___y_5551__boxed_135_, v_x_133_);
lean_dec(v_x_133_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_139_, lean_object* v_msgData_140_, uint8_t v_severity_141_, uint8_t v_isSilent_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_185_; uint8_t v___y_186_; uint8_t v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; uint8_t v___y_190_; lean_object* v___y_191_; lean_object* v___y_211_; uint8_t v___y_212_; uint8_t v___y_213_; lean_object* v___y_214_; uint8_t v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_221_; uint8_t v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; uint8_t v___x_231_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; uint8_t v___y_237_; uint8_t v___y_238_; uint8_t v___y_240_; uint8_t v___x_254_; 
v___x_231_ = 2;
v___x_254_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_231_);
if (v___x_254_ == 0)
{
v___y_240_ = v___x_254_;
goto v___jp_239_;
}
else
{
uint8_t v___x_255_; 
lean_inc_ref(v_msgData_140_);
v___x_255_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_140_);
v___y_240_ = v___x_255_;
goto v___jp_239_;
}
v___jp_148_:
{
lean_object* v___x_158_; lean_object* v_currNamespace_159_; lean_object* v_openDecls_160_; lean_object* v_env_161_; lean_object* v_nextMacroScope_162_; lean_object* v_ngen_163_; lean_object* v_auxDeclNGen_164_; lean_object* v_traceState_165_; lean_object* v_cache_166_; lean_object* v_messages_167_; lean_object* v_infoState_168_; lean_object* v_snapshotTasks_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_183_; 
v___x_158_ = lean_st_ref_take(v___y_157_);
v_currNamespace_159_ = lean_ctor_get(v___y_156_, 5);
v_openDecls_160_ = lean_ctor_get(v___y_156_, 6);
v_env_161_ = lean_ctor_get(v___x_158_, 0);
v_nextMacroScope_162_ = lean_ctor_get(v___x_158_, 1);
v_ngen_163_ = lean_ctor_get(v___x_158_, 2);
v_auxDeclNGen_164_ = lean_ctor_get(v___x_158_, 3);
v_traceState_165_ = lean_ctor_get(v___x_158_, 4);
v_cache_166_ = lean_ctor_get(v___x_158_, 5);
v_messages_167_ = lean_ctor_get(v___x_158_, 6);
v_infoState_168_ = lean_ctor_get(v___x_158_, 7);
v_snapshotTasks_169_ = lean_ctor_get(v___x_158_, 8);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_183_ == 0)
{
v___x_171_ = v___x_158_;
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_snapshotTasks_169_);
lean_inc(v_infoState_168_);
lean_inc(v_messages_167_);
lean_inc(v_cache_166_);
lean_inc(v_traceState_165_);
lean_inc(v_auxDeclNGen_164_);
lean_inc(v_ngen_163_);
lean_inc(v_nextMacroScope_162_);
lean_inc(v_env_161_);
lean_dec(v___x_158_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
lean_inc(v_openDecls_160_);
lean_inc(v_currNamespace_159_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_currNamespace_159_);
lean_ctor_set(v___x_173_, 1, v_openDecls_160_);
v___x_174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___y_155_);
lean_inc_ref(v___y_153_);
lean_inc_ref(v___y_151_);
v___x_175_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_175_, 0, v___y_151_);
lean_ctor_set(v___x_175_, 1, v___y_150_);
lean_ctor_set(v___x_175_, 2, v___y_154_);
lean_ctor_set(v___x_175_, 3, v___y_153_);
lean_ctor_set(v___x_175_, 4, v___x_174_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5, v___y_152_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5 + 1, v___y_149_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5 + 2, v_isSilent_142_);
v___x_176_ = l_Lean_MessageLog_add(v___x_175_, v_messages_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 6, v___x_176_);
v___x_178_ = v___x_171_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_env_161_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_nextMacroScope_162_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_ngen_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_auxDeclNGen_164_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_traceState_165_);
lean_ctor_set(v_reuseFailAlloc_182_, 5, v_cache_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 6, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_182_, 7, v_infoState_168_);
lean_ctor_set(v_reuseFailAlloc_182_, 8, v_snapshotTasks_169_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_st_ref_put(v___y_157_, v___x_178_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
v___jp_184_:
{
lean_object* v_fileName_192_; lean_object* v_fileMap_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_209_; 
v_fileName_192_ = lean_ctor_get(v___y_188_, 0);
v_fileMap_193_ = lean_ctor_get(v___y_188_, 1);
v___x_194_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_140_);
v___x_195_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v___x_194_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_209_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_209_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_209_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc_ref_n(v_fileMap_193_, 2);
v___x_200_ = l_Lean_FileMap_toPosition(v_fileMap_193_, v___y_189_);
lean_dec(v___y_189_);
v___x_201_ = l_Lean_FileMap_toPosition(v_fileMap_193_, v___y_191_);
lean_dec(v___y_191_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_190_ == 0)
{
lean_del_object(v___x_198_);
lean_dec_ref(v___y_185_);
v___y_149_ = v___y_186_;
v___y_150_ = v___x_200_;
v___y_151_ = v_fileName_192_;
v___y_152_ = v___y_187_;
v___y_153_ = v___x_203_;
v___y_154_ = v___x_202_;
v___y_155_ = v_a_196_;
v___y_156_ = v___y_145_;
v___y_157_ = v___y_146_;
goto v___jp_148_;
}
else
{
uint8_t v___x_204_; 
lean_inc(v_a_196_);
v___x_204_ = l_Lean_MessageData_hasTag(v___y_185_, v_a_196_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec_ref_known(v___x_202_, 1);
lean_dec_ref(v___x_200_);
lean_dec(v_a_196_);
v___x_205_ = lean_box(0);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_205_);
v___x_207_ = v___x_198_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_del_object(v___x_198_);
v___y_149_ = v___y_186_;
v___y_150_ = v___x_200_;
v___y_151_ = v_fileName_192_;
v___y_152_ = v___y_187_;
v___y_153_ = v___x_203_;
v___y_154_ = v___x_202_;
v___y_155_ = v_a_196_;
v___y_156_ = v___y_145_;
v___y_157_ = v___y_146_;
goto v___jp_148_;
}
}
}
}
v___jp_210_:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Syntax_getTailPos_x3f(v___y_216_, v___y_213_);
lean_dec(v___y_216_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_inc(v___y_217_);
v___y_185_ = v___y_211_;
v___y_186_ = v___y_212_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_214_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_215_;
v___y_191_ = v___y_217_;
goto v___jp_184_;
}
else
{
lean_object* v_val_219_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_218_, 1);
v___y_185_ = v___y_211_;
v___y_186_ = v___y_212_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_214_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_215_;
v___y_191_ = v_val_219_;
goto v___jp_184_;
}
}
v___jp_220_:
{
lean_object* v_ref_227_; lean_object* v___x_228_; 
v_ref_227_ = l_Lean_replaceRef(v_ref_139_, v___y_224_);
v___x_228_ = l_Lean_Syntax_getPos_x3f(v_ref_227_, v___y_222_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___y_211_ = v___y_221_;
v___y_212_ = v___y_226_;
v___y_213_ = v___y_222_;
v___y_214_ = v___y_223_;
v___y_215_ = v___y_225_;
v___y_216_ = v_ref_227_;
v___y_217_ = v___x_229_;
goto v___jp_210_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
v___y_211_ = v___y_221_;
v___y_212_ = v___y_226_;
v___y_213_ = v___y_222_;
v___y_214_ = v___y_223_;
v___y_215_ = v___y_225_;
v___y_216_ = v_ref_227_;
v___y_217_ = v_val_230_;
goto v___jp_210_;
}
}
v___jp_232_:
{
if (v___y_238_ == 0)
{
v___y_221_ = v___y_235_;
v___y_222_ = v___y_237_;
v___y_223_ = v___y_234_;
v___y_224_ = v___y_233_;
v___y_225_ = v___y_236_;
v___y_226_ = v_severity_141_;
goto v___jp_220_;
}
else
{
v___y_221_ = v___y_235_;
v___y_222_ = v___y_237_;
v___y_223_ = v___y_234_;
v___y_224_ = v___y_233_;
v___y_225_ = v___y_236_;
v___y_226_ = v___x_231_;
goto v___jp_220_;
}
}
v___jp_239_:
{
if (v___y_240_ == 0)
{
lean_object* v_toCold_241_; lean_object* v_options_242_; lean_object* v_ref_243_; uint8_t v_suppressElabErrors_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; uint8_t v___x_248_; uint8_t v___x_249_; 
v_toCold_241_ = lean_ctor_get(v___y_145_, 0);
v_options_242_ = lean_ctor_get(v___y_145_, 1);
v_ref_243_ = lean_ctor_get(v___y_145_, 4);
v_suppressElabErrors_244_ = lean_ctor_get_uint8(v___y_145_, sizeof(void*)*10 + 1);
v___x_245_ = lean_box(v_suppressElabErrors_244_);
v___x_246_ = lean_box(v___y_240_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v___x_245_);
lean_closure_set(v___f_247_, 1, v___x_246_);
v___x_248_ = 1;
v___x_249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_248_);
if (v___x_249_ == 0)
{
v___y_233_ = v_ref_243_;
v___y_234_ = v_toCold_241_;
v___y_235_ = v___f_247_;
v___y_236_ = v_suppressElabErrors_244_;
v___y_237_ = v___y_240_;
v___y_238_ = v___x_249_;
goto v___jp_232_;
}
else
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Lean_warningAsError;
v___x_251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__5(v_options_242_, v___x_250_);
v___y_233_ = v_ref_243_;
v___y_234_ = v_toCold_241_;
v___y_235_ = v___f_247_;
v___y_236_ = v_suppressElabErrors_244_;
v___y_237_ = v___y_240_;
v___y_238_ = v___x_251_;
goto v___jp_232_;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_msgData_140_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_256_, lean_object* v_msgData_257_, lean_object* v_severity_258_, lean_object* v_isSilent_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v_severity_boxed_265_; uint8_t v_isSilent_boxed_266_; lean_object* v_res_267_; 
v_severity_boxed_265_ = lean_unbox(v_severity_258_);
v_isSilent_boxed_266_ = lean_unbox(v_isSilent_259_);
v_res_267_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_256_, v_msgData_257_, v_severity_boxed_265_, v_isSilent_boxed_266_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v_ref_256_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(lean_object* v_ref_268_, lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = 1;
v___x_280_ = 0;
v___x_281_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3___redArg(v_ref_268_, v_msgData_269_, v___x_279_, v___x_280_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2___boxed(lean_object* v_ref_282_, lean_object* v_msgData_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_ref_282_, v_msgData_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v_ref_282_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__2));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(lean_object* v_linterOption_300_, lean_object* v_stx_301_, lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_name_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_330_; 
v_name_312_ = lean_ctor_get(v_linterOption_300_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_linterOption_300_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_linterOption_300_, 1);
lean_dec(v_unused_331_);
v___x_314_ = v_linterOption_300_;
v_isShared_315_ = v_isSharedCheck_330_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_name_312_);
lean_dec(v_linterOption_300_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_330_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__1);
lean_inc(v_name_312_);
v___x_317_ = l_Lean_MessageData_ofName(v_name_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 7);
lean_ctor_set(v___x_314_, 1, v___x_317_);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_329_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_disable_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_320_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___closed__3);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v_disable_322_ = l_Lean_MessageData_note(v___x_321_);
v___x_323_ = l_Lean_Linter_linterMessageTag;
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v_msg_302_);
lean_ctor_set(v___x_324_, 1, v_disable_322_);
v___x_325_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_326_, 0, v_name_312_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_inc(v_stx_301_);
v___x_327_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_327_, 0, v_stx_301_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2(v_stx_301_, v___x_327_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v_stx_301_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1___boxed(lean_object* v_linterOption_332_, lean_object* v_stx_333_, lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v_linterOption_332_, v_stx_333_, v_msg_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(lean_object* v_o_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v___x_350_; lean_object* v_toEnvExtension_351_; lean_object* v_asyncMode_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_merged_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v___x_348_ = lean_st_ref_get(v___y_346_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_env_349_);
lean_dec(v___x_348_);
v___x_350_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_351_ = lean_ctor_get(v___x_350_, 0);
v_asyncMode_352_ = lean_ctor_get(v_toEnvExtension_351_, 2);
v___x_353_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_354_ = lean_box(0);
v___x_355_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_353_, v___x_350_, v_env_349_, v_asyncMode_352_, v___x_354_);
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
lean_ctor_set(v___x_358_, 0, v_o_345_);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_o_345_);
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
lean_object* v_options_379_; lean_object* v___x_380_; 
v_options_379_ = lean_ctor_get(v___y_376_, 1);
lean_inc_ref(v_options_379_);
v___x_380_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__0_spec__0___redArg(v_options_379_, v___y_377_);
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
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_del_object(v___x_417_);
v___x_425_ = lean_box(0);
lean_inc(v_replacement_404_);
v___x_426_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_402_, v_replacement_404_, v___x_425_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__1);
v___x_429_ = lean_unbox(v_a_427_);
lean_dec(v_a_427_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_replacement_404_);
v___x_430_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1(v___x_419_, v_ref_403_, v___x_428_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
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
lean_ctor_set(v___x_433_, 1, v___x_425_);
lean_ctor_set(v___x_433_, 2, v___x_425_);
lean_ctor_set(v___x_433_, 3, v___x_425_);
lean_ctor_set(v___x_433_, 4, v___x_425_);
lean_ctor_set(v___x_433_, 5, v___x_425_);
lean_inc(v_ref_403_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_ref_403_);
v___x_435_ = 4;
lean_inc_ref(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_436_, 0, v___x_433_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_425_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*3, v___x_435_);
v___x_437_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa___closed__6);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_440_ = lean_array_push(v___x_439_, v___x_436_);
v___x_441_ = 0;
v___x_442_ = l_Lean_MessageData_hint(v___x_437_, v___x_440_, v___x_434_, v___x_425_, v___x_441_, v_a_411_, v_a_412_);
lean_dec_ref(v___x_440_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_428_);
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
v_a_454_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_426_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_426_);
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
v_ref_567_ = lean_ctor_get(v___y_564_, 4);
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
lean_inc(v_a_628_);
v___x_658_ = l_Lean_Exception_isInterrupt(v_a_628_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_Exception_isRuntime(v_a_628_);
v___y_630_ = v___x_659_;
goto v___jp_629_;
}
else
{
lean_dec(v_a_628_);
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
lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___x_803_; 
v___x_803_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_724_, v___y_726_, v___y_728_, v___y_730_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
v___x_805_ = lean_apply_9(v_rewrite_718_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, lean_box(0));
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_807_, 0, v___f_719_);
lean_closure_set(v___f_807_, 1, v_close_720_);
lean_closure_set(v___f_807_, 2, v_a_806_);
v___x_808_ = l_Lean_Elab_Tactic_focus___redArg(v___f_807_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_810_) == 0)
{
uint8_t v___x_811_; 
v___x_811_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
if (v___x_811_ == 0)
{
lean_dec_ref_known(v___x_810_, 1);
lean_dec(v_a_804_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
v___y_733_ = v___y_723_;
v___y_734_ = v___y_724_;
v___y_735_ = v___y_725_;
v___y_736_ = v___y_726_;
v___y_737_ = v___y_727_;
v___y_738_ = v___y_728_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
goto v___jp_732_;
}
else
{
lean_object* v_a_812_; uint8_t v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_810_, 1);
v___x_813_ = l_List_isEmpty___redArg(v_a_812_);
lean_dec(v_a_812_);
if (v___x_813_ == 0)
{
lean_dec(v_a_804_);
lean_dec(v_replacement_722_);
lean_dec(v_ref_721_);
v___y_733_ = v___y_723_;
v___y_734_ = v___y_724_;
v___y_735_ = v___y_725_;
v___y_736_ = v___y_726_;
v___y_737_ = v___y_727_;
v___y_738_ = v___y_728_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
goto v___jp_732_;
}
else
{
lean_object* v___x_814_; 
v___x_814_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa(v_a_804_, v_ref_721_, v_replacement_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref_known(v___x_814_, 1);
v___y_733_ = v___y_723_;
v___y_734_ = v___y_724_;
v___y_735_ = v___y_725_;
v___y_736_ = v___y_726_;
v___y_737_ = v___y_727_;
v___y_738_ = v___y_728_;
v___y_739_ = v___y_729_;
v___y_740_ = v___y_730_;
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
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_a_809_);
lean_dec(v_a_804_);
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
v_a_815_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_810_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_810_);
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
lean_dec(v_a_804_);
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
v_a_823_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_808_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_808_);
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
lean_dec(v_a_804_);
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
v_a_831_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_805_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_805_);
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
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
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
v_a_839_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_803_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_803_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
v___jp_732_:
{
lean_object* v_ref_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_ref_741_ = lean_ctor_get(v___y_739_, 4);
v___x_742_ = 0;
v___x_743_ = l_Lean_SourceInfo_fromRef(v_ref_741_, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__2));
lean_inc_n(v___x_743_, 37);
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_743_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__5));
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__7));
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__4));
v___x_751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__5));
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_743_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__6));
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__7));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_743_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
v___x_756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__9));
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__10));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_743_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__2));
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__3));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_743_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__11));
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__12));
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_743_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___x_743_, v___x_762_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node2(v___x_743_, v___x_759_, v___x_761_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_771_);
lean_inc_ref_n(v___x_758_, 2);
v___x_773_ = l_Lean_Syntax_node2(v___x_743_, v___x_756_, v___x_758_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__12));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_743_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
v___x_777_ = l_Lean_Syntax_node1(v___x_743_, v___x_775_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node2(v___x_743_, v___x_756_, v___x_758_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__13));
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__14));
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_743_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
v___x_785_ = l_Lean_Syntax_node1(v___x_743_, v___x_783_, v___x_784_);
v___x_786_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___x_743_, v___x_756_, v___x_758_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node3(v___x_743_, v___x_749_, v___x_773_, v___x_781_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node2(v___x_743_, v___x_754_, v___x_755_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__15));
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_743_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_Syntax_node3(v___x_743_, v___x_750_, v___x_752_, v___x_794_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node1(v___x_743_, v___x_749_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node1(v___x_743_, v___x_748_, v___x_798_);
v___x_800_ = l_Lean_Syntax_node1(v___x_743_, v___x_747_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node2(v___x_743_, v___x_744_, v___x_746_, v___x_800_);
v___x_802_ = l_Lean_Elab_Tactic_evalTactic(v___x_801_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed(lean_object* v_rewrite_847_, lean_object* v___f_848_, lean_object* v_close_849_, lean_object* v_ref_850_, lean_object* v_replacement_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2(v_rewrite_847_, v___f_848_, v_close_849_, v_ref_850_, v_replacement_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(lean_object* v_ref_863_, lean_object* v_rewrite_864_, lean_object* v_replacement_865_, lean_object* v_close_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; 
v___f_876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___closed__0));
v___f_877_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___boxed), 14, 5);
lean_closure_set(v___f_877_, 0, v_rewrite_864_);
lean_closure_set(v___f_877_, 1, v___f_876_);
lean_closure_set(v___f_877_, 2, v_close_866_);
lean_closure_set(v___f_877_, 3, v_ref_863_);
lean_closure_set(v___f_877_, 4, v_replacement_865_);
v___x_878_ = l_Lean_Elab_Tactic_focus___redArg(v___f_877_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___boxed(lean_object* v_ref_879_, lean_object* v_rewrite_880_, lean_object* v_replacement_881_, lean_object* v_close_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_879_, v_rewrite_880_, v_replacement_881_, v_close_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(lean_object* v_00_u03b1_893_, lean_object* v_ref_894_, lean_object* v_rewrite_895_, lean_object* v_replacement_896_, lean_object* v_close_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_ref_894_, v_rewrite_895_, v_replacement_896_, v_close_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___boxed(lean_object* v_00_u03b1_908_, lean_object* v_ref_909_, lean_object* v_rewrite_910_, lean_object* v_replacement_911_, lean_object* v_close_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore(v_00_u03b1_908_, v_ref_909_, v_rewrite_910_, v_replacement_911_, v_close_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_ref_929_; lean_object* v___x_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_ref_929_ = lean_ctor_get(v___y_926_, 4);
v___x_930_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_logUnnecessaryRwa_spec__1_spec__2_spec__3_spec__4(v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_inc(v_ref_929_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_ref_929_);
lean_ctor_set(v___x_935_, 1, v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg___boxed(lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__3));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__5));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(lean_object* v_fvarId_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_960_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___x_982_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_mkFVar(v_fvarId_958_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc_ref(v___x_970_);
v___x_982_ = lean_infer_type(v___x_970_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_MVarId_getType(v_a_969_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; uint8_t v_a_987_; lean_object* v___x_1007_; uint8_t v_foApprox_1008_; uint8_t v_ctxApprox_1009_; uint8_t v_quasiPatternApprox_1010_; uint8_t v_constApprox_1011_; uint8_t v_isDefEqStuckEx_1012_; uint8_t v_unificationHints_1013_; uint8_t v_proofIrrelevance_1014_; uint8_t v_offsetCnstrs_1015_; uint8_t v_transparency_1016_; uint8_t v_etaStruct_1017_; uint8_t v_univApprox_1018_; uint8_t v_iota_1019_; uint8_t v_beta_1020_; uint8_t v_proj_1021_; uint8_t v_zeta_1022_; uint8_t v_zetaDelta_1023_; uint8_t v_zetaUnused_1024_; uint8_t v_zetaHave_1025_; uint8_t v_canUnfoldPredicateConfig_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1060_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_1007_ = l_Lean_Meta_Context_config(v___y_963_);
v_foApprox_1008_ = lean_ctor_get_uint8(v___x_1007_, 0);
v_ctxApprox_1009_ = lean_ctor_get_uint8(v___x_1007_, 1);
v_quasiPatternApprox_1010_ = lean_ctor_get_uint8(v___x_1007_, 2);
v_constApprox_1011_ = lean_ctor_get_uint8(v___x_1007_, 3);
v_isDefEqStuckEx_1012_ = lean_ctor_get_uint8(v___x_1007_, 4);
v_unificationHints_1013_ = lean_ctor_get_uint8(v___x_1007_, 5);
v_proofIrrelevance_1014_ = lean_ctor_get_uint8(v___x_1007_, 6);
v_offsetCnstrs_1015_ = lean_ctor_get_uint8(v___x_1007_, 8);
v_transparency_1016_ = lean_ctor_get_uint8(v___x_1007_, 9);
v_etaStruct_1017_ = lean_ctor_get_uint8(v___x_1007_, 10);
v_univApprox_1018_ = lean_ctor_get_uint8(v___x_1007_, 11);
v_iota_1019_ = lean_ctor_get_uint8(v___x_1007_, 12);
v_beta_1020_ = lean_ctor_get_uint8(v___x_1007_, 13);
v_proj_1021_ = lean_ctor_get_uint8(v___x_1007_, 14);
v_zeta_1022_ = lean_ctor_get_uint8(v___x_1007_, 15);
v_zetaDelta_1023_ = lean_ctor_get_uint8(v___x_1007_, 16);
v_zetaUnused_1024_ = lean_ctor_get_uint8(v___x_1007_, 17);
v_zetaHave_1025_ = lean_ctor_get_uint8(v___x_1007_, 18);
v_canUnfoldPredicateConfig_1026_ = lean_ctor_get_uint8(v___x_1007_, 19);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1028_ = v___x_1007_;
v_isShared_1029_ = v_isSharedCheck_1060_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v___x_1007_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1060_;
goto v_resetjp_1027_;
}
v___jp_986_:
{
if (v_a_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_box(0);
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__2));
v___x_990_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_983_, v_a_985_, v___x_988_, v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__4);
v___x_993_ = l_Lean_indentExpr(v___x_970_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__6);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_a_991_);
v___x_998_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v___x_997_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v___x_998_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v___x_970_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
v_a_999_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_990_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_dec(v_a_985_);
lean_dec(v_a_983_);
v___y_972_ = v___y_960_;
v___y_973_ = v___y_961_;
v___y_974_ = v___y_962_;
v___y_975_ = v___y_963_;
v___y_976_ = v___y_964_;
v___y_977_ = v___y_965_;
v___y_978_ = v___y_966_;
goto v___jp_971_;
}
}
v_resetjp_1027_:
{
uint8_t v_trackZetaDelta_1030_; lean_object* v_zetaDeltaSet_1031_; lean_object* v_lctx_1032_; lean_object* v_localInstances_1033_; lean_object* v_defEqCtx_x3f_1034_; lean_object* v_synthPendingDepth_1035_; lean_object* v_customCanUnfoldPredicate_x3f_1036_; uint8_t v_univApprox_1037_; uint8_t v_inTypeClassResolution_1038_; uint8_t v_cacheInferType_1039_; uint8_t v___x_1040_; lean_object* v___x_1042_; 
v_trackZetaDelta_1030_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*7);
v_zetaDeltaSet_1031_ = lean_ctor_get(v___y_963_, 1);
v_lctx_1032_ = lean_ctor_get(v___y_963_, 2);
v_localInstances_1033_ = lean_ctor_get(v___y_963_, 3);
v_defEqCtx_x3f_1034_ = lean_ctor_get(v___y_963_, 4);
v_synthPendingDepth_1035_ = lean_ctor_get(v___y_963_, 5);
v_customCanUnfoldPredicate_x3f_1036_ = lean_ctor_get(v___y_963_, 6);
v_univApprox_1037_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1038_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*7 + 2);
v_cacheInferType_1039_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*7 + 3);
v___x_1040_ = 1;
if (v_isShared_1029_ == 0)
{
v___x_1042_ = v___x_1028_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 0, v_foApprox_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 1, v_ctxApprox_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 2, v_quasiPatternApprox_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 3, v_constApprox_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 4, v_isDefEqStuckEx_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 5, v_unificationHints_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 6, v_proofIrrelevance_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 8, v_offsetCnstrs_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 9, v_transparency_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 10, v_etaStruct_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 11, v_univApprox_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 12, v_iota_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 13, v_beta_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 14, v_proj_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 15, v_zeta_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 16, v_zetaDelta_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 17, v_zetaUnused_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 18, v_zetaHave_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, 19, v_canUnfoldPredicateConfig_1026_);
v___x_1042_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
uint64_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_ctor_set_uint8(v___x_1042_, 7, v___x_1040_);
v___x_1043_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set_uint64(v___x_1044_, sizeof(void*)*1, v___x_1043_);
lean_inc(v_customCanUnfoldPredicate_x3f_1036_);
lean_inc(v_synthPendingDepth_1035_);
lean_inc(v_defEqCtx_x3f_1034_);
lean_inc_ref(v_localInstances_1033_);
lean_inc_ref(v_lctx_1032_);
lean_inc(v_zetaDeltaSet_1031_);
v___x_1045_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_zetaDeltaSet_1031_);
lean_ctor_set(v___x_1045_, 2, v_lctx_1032_);
lean_ctor_set(v___x_1045_, 3, v_localInstances_1033_);
lean_ctor_set(v___x_1045_, 4, v_defEqCtx_x3f_1034_);
lean_ctor_set(v___x_1045_, 5, v_synthPendingDepth_1035_);
lean_ctor_set(v___x_1045_, 6, v_customCanUnfoldPredicate_x3f_1036_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*7, v_trackZetaDelta_1030_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*7 + 1, v_univApprox_1037_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1038_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*7 + 3, v_cacheInferType_1039_);
lean_inc(v_a_985_);
lean_inc(v_a_983_);
v___x_1046_ = l_Lean_Meta_isExprDefEq(v_a_983_, v_a_985_, v___x_1045_, v___y_964_, v___y_965_, v___y_966_);
lean_dec_ref_known(v___x_1045_, 7);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; uint8_t v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = lean_unbox(v_a_1047_);
lean_dec(v_a_1047_);
v_a_987_ = v___x_1048_;
goto v___jp_986_;
}
else
{
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1049_; uint8_t v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1050_ = lean_unbox(v_a_1049_);
lean_dec(v_a_1049_);
v_a_987_ = v___x_1050_;
goto v___jp_986_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_985_);
lean_dec(v_a_983_);
lean_dec_ref(v___x_970_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
v_a_1051_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1046_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1046_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_983_);
lean_dec_ref(v___x_970_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
v_a_1061_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_984_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_984_);
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
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___x_970_);
lean_dec(v_a_969_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
v_a_1069_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_982_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_982_);
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
v___jp_971_:
{
lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___closed__1));
v___x_980_ = 1;
v___x_981_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_979_, v___x_970_, v___x_980_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v___x_981_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v_fvarId_958_);
v_a_1077_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_968_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_968_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed(lean_object* v_fvarId_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0(v_fvarId_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(lean_object* v_fvarId_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; 
v___f_1106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1106_, 0, v_fvarId_1096_);
v___x_1107_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1106_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar___boxed(lean_object* v_fvarId_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar(v_fvarId_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(lean_object* v_00_u03b1_1119_, lean_object* v_msg_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___redArg(v_msg_1120_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_msg_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_closeUsingFVar_spec__0(v_00_u03b1_1131_, v_msg_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1142_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg(){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___closed__0);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg___boxed(lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(lean_object* v_00_u03b1_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___boxed(lean_object* v_00_u03b1_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0(v_00_u03b1_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0(lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_ref_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_ref_1182_ = lean_ctor_get(v___y_1179_, 4);
v___x_1183_ = 0;
v___x_1184_ = l_Lean_SourceInfo_fromRef(v_ref_1182_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__0___boxed(lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1(lean_object* v___f_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
v___x_1210_ = lean_apply_9(v___f_1196_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, lean_box(0));
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_n(v_a_1211_, 2);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__2___closed__11));
v___x_1213_ = l_Lean_Name_mkStr4(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
v___x_1215_ = l_Lean_Syntax_node1(v_a_1211_, v___x_1213_, v___x_1214_);
v___x_1216_ = l_Lean_Elab_Tactic_evalTactic(v___x_1215_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
lean_dec_ref(v___x_1197_);
v_a_1217_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1210_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___lam__1___boxed(lean_object* v___f_1225_, lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v_x_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Elab_Tactic_evalRwa___lam__1(v___f_1225_, v___x_1226_, v___x_1227_, v___x_1228_, v_x_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRwa___closed__7(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Array_mkArray0(lean_box(0));
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa(lean_object* v_stx_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
lean_inc(v_stx_1278_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v_stx_1278_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_stx_1278_);
v___x_1290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = l_Lean_Syntax_getArg(v_stx_1278_, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1292_);
v___x_1294_ = l_Lean_Syntax_isOfKind(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec(v___x_1292_);
lean_dec(v_stx_1278_);
v___x_1295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1295_;
}
else
{
lean_object* v_ref_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_ref_1296_ = lean_ctor_get(v_a_1285_, 4);
v___x_1297_ = 0;
v___x_1298_ = l_Lean_SourceInfo_fromRef(v_ref_1296_, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__4));
lean_inc_n(v___x_1298_, 3);
v___x_1300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = l_Lean_Elab_Tactic_evalRwa___lam__0(v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_n(v_a_1302_, 4);
lean_dec_ref(v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__6));
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__7, &l_Lean_Elab_Tactic_evalRwa___closed__7_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__7);
v___x_1306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1298_);
lean_ctor_set(v___x_1306_, 1, v___x_1304_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
v___f_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__8));
v___x_1308_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__10));
lean_inc_ref(v___x_1306_);
v___x_1309_ = l_Lean_Syntax_node1(v___x_1298_, v___x_1308_, v___x_1306_);
lean_inc(v___x_1292_);
v___x_1310_ = l_Lean_Syntax_node4(v___x_1298_, v___x_1303_, v___x_1300_, v___x_1309_, v___x_1292_, v___x_1306_);
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
v___x_1313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1302_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1302_);
lean_ctor_set(v___x_1314_, 1, v___x_1304_);
lean_ctor_set(v___x_1314_, 2, v___x_1305_);
lean_inc_ref(v___x_1314_);
v___x_1315_ = l_Lean_Syntax_node1(v_a_1302_, v___x_1308_, v___x_1314_);
v___x_1316_ = l_Lean_Syntax_node4(v_a_1302_, v___x_1311_, v___x_1313_, v___x_1315_, v___x_1292_, v___x_1314_);
v___x_1317_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_1317_, 0, v___x_1310_);
v___x_1318_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1278_, v___x_1317_, v___x_1316_, v___f_1307_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwa___boxed(lean_object* v_stx_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_Tactic_evalRwa(v_stx_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1(){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1337_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__0));
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___closed__1));
v___x_1340_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwa___boxed), 10, 0);
v___x_1341_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1337_, v___x_1338_, v___x_1339_, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1___boxed(lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwa___regBuiltin_Lean_Elab_Tactic_evalRwa__1();
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0(uint8_t v___x_1344_, lean_object* v_fvarId_1345_, uint8_t v_symm_1346_, lean_object* v_term_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = 2;
v___x_1358_ = lean_box(0);
v___x_1359_ = 0;
v___x_1360_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1, v___x_1357_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 1, v___x_1344_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 2, v___x_1359_);
v___x_1361_ = l_Lean_Elab_Tactic_rewriteLocalDeclCore(v_term_1347_, v_symm_1346_, v_fvarId_1345_, v___x_1360_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed(lean_object* v___x_1362_, lean_object* v_fvarId_1363_, lean_object* v_symm_1364_, lean_object* v_term_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_2490__boxed_1375_; uint8_t v_symm_boxed_1376_; lean_object* v_res_1377_; 
v___x_2490__boxed_1375_ = lean_unbox(v___x_1362_);
v_symm_boxed_1376_ = lean_unbox(v_symm_1364_);
v_res_1377_ = l_Lean_Elab_Tactic_evalRwaAt___lam__0(v___x_2490__boxed_1375_, v_fvarId_1363_, v_symm_boxed_1376_, v_term_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1(lean_object* v___x_1378_, lean_object* v_stx_1379_, lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___f_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Elab_Tactic_getFVarId(v___x_1378_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = l_Lean_Syntax_getArg(v_stx_1379_, v___x_1380_);
v___x_1395_ = l_Lean_Elab_Tactic_foldRWRulesSeq___redArg(v___x_1394_, v___x_1381_, v_a_1393_, v___f_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1395_;
}
else
{
lean_dec_ref(v___f_1382_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed(lean_object* v___x_1396_, lean_object* v_stx_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v___f_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Elab_Tactic_evalRwaAt___lam__1(v___x_1396_, v_stx_1397_, v___x_1398_, v___x_1399_, v___f_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___x_1399_);
lean_dec(v___x_1398_);
lean_dec(v_stx_1397_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt(lean_object* v_stx_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
lean_inc(v_stx_1431_);
v___x_1442_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_stx_1431_);
v___x_1443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__2));
lean_inc(v___x_1445_);
v___x_1447_ = l_Lean_Syntax_isOfKind(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec(v___x_1445_);
lean_dec(v_stx_1431_);
v___x_1448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRwa_spec__0___redArg();
return v___x_1448_;
}
else
{
lean_object* v_ref_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_ref_1449_ = lean_ctor_get(v_a_1438_, 4);
v___x_1450_ = lean_box(v___x_1447_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1451_, 0, v___x_1450_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_unsigned_to_nat(3u);
v___x_1454_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1453_);
lean_inc(v___x_1445_);
lean_inc(v_stx_1431_);
lean_inc(v___x_1454_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1455_, 0, v___x_1454_);
lean_closure_set(v___f_1455_, 1, v_stx_1431_);
lean_closure_set(v___f_1455_, 2, v___x_1452_);
lean_closure_set(v___f_1455_, 3, v___x_1445_);
lean_closure_set(v___f_1455_, 4, v___f_1451_);
v___x_1456_ = 0;
v___x_1457_ = l_Lean_SourceInfo_fromRef(v_ref_1449_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__12));
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__13));
lean_inc_n(v___x_1457_, 8);
v___x_1460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwa___closed__10));
v___x_1462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg___lam__0___closed__9));
v___x_1463_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRwa___closed__7, &l_Lean_Elab_Tactic_evalRwa___closed__7_once, _init_l_Lean_Elab_Tactic_evalRwa___closed__7);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1457_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node1(v___x_1457_, v___x_1461_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__3));
v___x_1467_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__4));
v___x_1468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1457_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__6));
v___x_1470_ = l_Lean_Syntax_node1(v___x_1457_, v___x_1462_, v___x_1454_);
v___x_1471_ = l_Lean_Syntax_node1(v___x_1457_, v___x_1469_, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node2(v___x_1457_, v___x_1466_, v___x_1468_, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node1(v___x_1457_, v___x_1462_, v___x_1472_);
v___x_1474_ = l_Lean_Syntax_node4(v___x_1457_, v___x_1458_, v___x_1460_, v___x_1465_, v___x_1445_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__7));
v___x_1476_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaCore___redArg(v_stx_1431_, v___f_1455_, v___x_1474_, v___x_1475_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRwaAt___boxed(lean_object* v_stx_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Elab_Tactic_evalRwaAt(v_stx_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1(){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRwaAt___closed__1));
v___x_1497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___closed__1));
v___x_1498_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRwaAt___boxed), 10, 0);
v___x_1499_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1495_, v___x_1496_, v___x_1497_, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1___boxed(lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Elab_Tactic_Rwa_0__Lean_Elab_Tactic_evalRwaAt___regBuiltin_Lean_Elab_Tactic_evalRwaAt__1();
return v_res_1501_;
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
