// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Trace
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.Config import Lean.Elab.Tactic.Grind.Param import Lean.Meta.Tactic.TryThis import Lean.Meta.Tactic.Grind.Finish import Lean.Meta.Tactic.Grind.CollectParams import Lean.Meta.Sym.Grind
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_internalizeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkFinish(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkFinishTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toErrorMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symByContra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 214, 28, 119, 209, 102, 217, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "by_contra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "symIntros"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(51, 175, 114, 140, 112, 61, 143, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "generated tactic cannot close the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nInitial goal\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "finish\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(13, 105, 206, 35, 173, 234, 53, 204)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`finish\?` failed, but resulting goal is not available"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_saveState___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "finishTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 104, 221, 59, 99, 114, 168, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(186, 27, 67, 52, 119, 51, 108, 2)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(91, 188, 82, 28, 141, 159, 228, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 23, 221, 94, 250, 9, 160, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 10, 68, 183, 25, 215, 244, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 13, 146, 144, 74, 183, 56, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 20, 224, 46, 151, 65, 68, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalFinishTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(30, 0, 151, 159, 220, 77, 241, 66)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(lean_object* v_x_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_symSimpMethods_20_; lean_object* v_symDSimpMethods_21_; lean_object* v_identity_22_; lean_object* v_activeSolvers_23_; uint8_t v_filterFacts_24_; lean_object* v_relevantSymbols_25_; lean_object* v_anchorRefs_x3f_26_; uint8_t v_anchors_27_; uint8_t v_cheapCases_28_; uint8_t v_reportMVarIssue_29_; lean_object* v_splitSource_30_; lean_object* v_ematchDiagSource_31_; lean_object* v_symPrios_32_; lean_object* v_extensions_33_; uint8_t v_debug_34_; uint8_t v_ematchDiag_35_; uint8_t v_markInstances_36_; uint8_t v_lax_37_; uint8_t v_suggestions_38_; uint8_t v_locals_39_; lean_object* v_branches_40_; lean_object* v_splits_41_; lean_object* v_ematch_42_; lean_object* v_gen_43_; lean_object* v_genLocal_44_; lean_object* v_instances_45_; uint8_t v_matchEqs_46_; uint8_t v_splitMatch_47_; uint8_t v_splitIte_48_; uint8_t v_splitIndPred_49_; uint8_t v_splitImp_50_; uint8_t v_filterFacts_51_; lean_object* v_canonHeartbeats_52_; uint8_t v_ext_53_; uint8_t v_extAll_54_; uint8_t v_etaStruct_55_; uint8_t v_funext_56_; uint8_t v_lookahead_57_; uint8_t v_verbose_58_; uint8_t v_clean_59_; uint8_t v_qlia_60_; uint8_t v_mbtc_61_; uint8_t v_zetaDelta_62_; uint8_t v_zeta_63_; uint8_t v_distrib_64_; lean_object* v_maxChar_65_; uint8_t v_ring_66_; lean_object* v_ringSteps_67_; lean_object* v_ringMaxDegree_68_; uint8_t v_linarith_69_; uint8_t v_lia_70_; lean_object* v_liaSteps_71_; lean_object* v_liaReorders_72_; lean_object* v_liaReorderCases_73_; uint8_t v_hom_74_; uint8_t v_ac_75_; lean_object* v_acSteps_76_; lean_object* v_exp_77_; uint8_t v_abstractProof_78_; uint8_t v_inj_79_; uint8_t v_order_80_; lean_object* v_min_81_; lean_object* v_detailed_82_; uint8_t v_useSorry_83_; uint8_t v_revert_84_; uint8_t v_funCC_85_; uint8_t v_reducible_86_; lean_object* v_maxSuggestions_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_ctx_11_ = lean_ctor_get(v_a_2_, 1);
v_config_12_ = lean_ctor_get(v_ctx_11_, 4);
v_toContext_13_ = lean_ctor_get(v_a_2_, 0);
v_sctx_14_ = lean_ctor_get(v_a_2_, 2);
v_methods_15_ = lean_ctor_get(v_a_2_, 3);
v_params_16_ = lean_ctor_get(v_a_2_, 4);
v_sym_17_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*5);
v_simp_18_ = lean_ctor_get(v_ctx_11_, 0);
v_simpMethods_19_ = lean_ctor_get(v_ctx_11_, 1);
v_symSimpMethods_20_ = lean_ctor_get(v_ctx_11_, 2);
v_symDSimpMethods_21_ = lean_ctor_get(v_ctx_11_, 3);
v_identity_22_ = lean_ctor_get(v_ctx_11_, 5);
v_activeSolvers_23_ = lean_ctor_get(v_ctx_11_, 6);
v_filterFacts_24_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13);
v_relevantSymbols_25_ = lean_ctor_get(v_ctx_11_, 7);
v_anchorRefs_x3f_26_ = lean_ctor_get(v_ctx_11_, 8);
v_anchors_27_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13 + 1);
v_cheapCases_28_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13 + 2);
v_reportMVarIssue_29_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13 + 3);
v_splitSource_30_ = lean_ctor_get(v_ctx_11_, 9);
v_ematchDiagSource_31_ = lean_ctor_get(v_ctx_11_, 10);
v_symPrios_32_ = lean_ctor_get(v_ctx_11_, 11);
v_extensions_33_ = lean_ctor_get(v_ctx_11_, 12);
v_debug_34_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13 + 4);
v_ematchDiag_35_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*13 + 5);
v_markInstances_36_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 1);
v_lax_37_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 2);
v_suggestions_38_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 3);
v_locals_39_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 4);
v_branches_40_ = lean_ctor_get(v_config_12_, 0);
v_splits_41_ = lean_ctor_get(v_config_12_, 1);
v_ematch_42_ = lean_ctor_get(v_config_12_, 2);
v_gen_43_ = lean_ctor_get(v_config_12_, 3);
v_genLocal_44_ = lean_ctor_get(v_config_12_, 4);
v_instances_45_ = lean_ctor_get(v_config_12_, 5);
v_matchEqs_46_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 5);
v_splitMatch_47_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 6);
v_splitIte_48_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 7);
v_splitIndPred_49_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 8);
v_splitImp_50_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 9);
v_filterFacts_51_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 10);
v_canonHeartbeats_52_ = lean_ctor_get(v_config_12_, 6);
v_ext_53_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 11);
v_extAll_54_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 12);
v_etaStruct_55_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 13);
v_funext_56_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 14);
v_lookahead_57_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 15);
v_verbose_58_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 16);
v_clean_59_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 17);
v_qlia_60_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 18);
v_mbtc_61_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 19);
v_zetaDelta_62_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 20);
v_zeta_63_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 21);
v_distrib_64_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 22);
v_maxChar_65_ = lean_ctor_get(v_config_12_, 7);
v_ring_66_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 23);
v_ringSteps_67_ = lean_ctor_get(v_config_12_, 8);
v_ringMaxDegree_68_ = lean_ctor_get(v_config_12_, 9);
v_linarith_69_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 24);
v_lia_70_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 25);
v_liaSteps_71_ = lean_ctor_get(v_config_12_, 10);
v_liaReorders_72_ = lean_ctor_get(v_config_12_, 11);
v_liaReorderCases_73_ = lean_ctor_get(v_config_12_, 12);
v_hom_74_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 26);
v_ac_75_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 27);
v_acSteps_76_ = lean_ctor_get(v_config_12_, 13);
v_exp_77_ = lean_ctor_get(v_config_12_, 14);
v_abstractProof_78_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 28);
v_inj_79_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 29);
v_order_80_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 30);
v_min_81_ = lean_ctor_get(v_config_12_, 15);
v_detailed_82_ = lean_ctor_get(v_config_12_, 16);
v_useSorry_83_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 31);
v_revert_84_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 32);
v_funCC_85_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 33);
v_reducible_86_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*18 + 34);
v_maxSuggestions_87_ = lean_ctor_get(v_config_12_, 17);
v___x_88_ = 1;
lean_inc(v_maxSuggestions_87_);
lean_inc(v_detailed_82_);
lean_inc(v_min_81_);
lean_inc(v_exp_77_);
lean_inc(v_acSteps_76_);
lean_inc(v_liaReorderCases_73_);
lean_inc(v_liaReorders_72_);
lean_inc(v_liaSteps_71_);
lean_inc(v_ringMaxDegree_68_);
lean_inc(v_ringSteps_67_);
lean_inc(v_maxChar_65_);
lean_inc(v_canonHeartbeats_52_);
lean_inc(v_instances_45_);
lean_inc(v_genLocal_44_);
lean_inc(v_gen_43_);
lean_inc(v_ematch_42_);
lean_inc(v_splits_41_);
lean_inc(v_branches_40_);
v___x_89_ = lean_alloc_ctor(0, 18, 35);
lean_ctor_set(v___x_89_, 0, v_branches_40_);
lean_ctor_set(v___x_89_, 1, v_splits_41_);
lean_ctor_set(v___x_89_, 2, v_ematch_42_);
lean_ctor_set(v___x_89_, 3, v_gen_43_);
lean_ctor_set(v___x_89_, 4, v_genLocal_44_);
lean_ctor_set(v___x_89_, 5, v_instances_45_);
lean_ctor_set(v___x_89_, 6, v_canonHeartbeats_52_);
lean_ctor_set(v___x_89_, 7, v_maxChar_65_);
lean_ctor_set(v___x_89_, 8, v_ringSteps_67_);
lean_ctor_set(v___x_89_, 9, v_ringMaxDegree_68_);
lean_ctor_set(v___x_89_, 10, v_liaSteps_71_);
lean_ctor_set(v___x_89_, 11, v_liaReorders_72_);
lean_ctor_set(v___x_89_, 12, v_liaReorderCases_73_);
lean_ctor_set(v___x_89_, 13, v_acSteps_76_);
lean_ctor_set(v___x_89_, 14, v_exp_77_);
lean_ctor_set(v___x_89_, 15, v_min_81_);
lean_ctor_set(v___x_89_, 16, v_detailed_82_);
lean_ctor_set(v___x_89_, 17, v_maxSuggestions_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 1, v_markInstances_36_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 2, v_lax_37_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 3, v_suggestions_38_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 4, v_locals_39_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 5, v_matchEqs_46_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 6, v_splitMatch_47_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 7, v_splitIte_48_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 8, v_splitIndPred_49_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 9, v_splitImp_50_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 10, v_filterFacts_51_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 11, v_ext_53_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 12, v_extAll_54_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 13, v_etaStruct_55_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 14, v_funext_56_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 15, v_lookahead_57_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 16, v_verbose_58_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 17, v_clean_59_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 18, v_qlia_60_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 19, v_mbtc_61_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 20, v_zetaDelta_62_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 21, v_zeta_63_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 22, v_distrib_64_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 23, v_ring_66_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 24, v_linarith_69_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 25, v_lia_70_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 26, v_hom_74_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 27, v_ac_75_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 28, v_abstractProof_78_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 29, v_inj_79_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 30, v_order_80_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 31, v_useSorry_83_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 32, v_revert_84_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 33, v_funCC_85_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*18 + 34, v_reducible_86_);
lean_inc_ref(v_extensions_33_);
lean_inc_ref(v_symPrios_32_);
lean_inc(v_ematchDiagSource_31_);
lean_inc(v_splitSource_30_);
lean_inc(v_anchorRefs_x3f_26_);
lean_inc(v_relevantSymbols_25_);
lean_inc_ref(v_activeSolvers_23_);
lean_inc(v_identity_22_);
lean_inc_ref(v_symDSimpMethods_21_);
lean_inc_ref(v_symSimpMethods_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_90_ = lean_alloc_ctor(0, 13, 6);
lean_ctor_set(v___x_90_, 0, v_simp_18_);
lean_ctor_set(v___x_90_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_90_, 2, v_symSimpMethods_20_);
lean_ctor_set(v___x_90_, 3, v_symDSimpMethods_21_);
lean_ctor_set(v___x_90_, 4, v___x_89_);
lean_ctor_set(v___x_90_, 5, v_identity_22_);
lean_ctor_set(v___x_90_, 6, v_activeSolvers_23_);
lean_ctor_set(v___x_90_, 7, v_relevantSymbols_25_);
lean_ctor_set(v___x_90_, 8, v_anchorRefs_x3f_26_);
lean_ctor_set(v___x_90_, 9, v_splitSource_30_);
lean_ctor_set(v___x_90_, 10, v_ematchDiagSource_31_);
lean_ctor_set(v___x_90_, 11, v_symPrios_32_);
lean_ctor_set(v___x_90_, 12, v_extensions_33_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13, v_filterFacts_24_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13 + 1, v_anchors_27_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13 + 2, v_cheapCases_28_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13 + 3, v_reportMVarIssue_29_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13 + 4, v_debug_34_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*13 + 5, v_ematchDiag_35_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_91_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_91_, 0, v_toContext_13_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_ctor_set(v___x_91_, 2, v_sctx_14_);
lean_ctor_set(v___x_91_, 3, v_methods_15_);
lean_ctor_set(v___x_91_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_92_ = lean_apply_9(v_x_1_, v___x_91_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_104_, lean_object* v_x_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_116_, lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_116_, v_x_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
lean_object* v_name_130_; lean_object* v_defValue_131_; lean_object* v_map_132_; lean_object* v___x_133_; 
v_name_130_ = lean_ctor_get(v_opt_129_, 0);
v_defValue_131_ = lean_ctor_get(v_opt_129_, 1);
v_map_132_ = lean_ctor_get(v_opts_128_, 0);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_132_, v_name_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = lean_unbox(v_defValue_131_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; 
v_val_135_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v___x_133_, 1);
if (lean_obj_tag(v_val_135_) == 1)
{
uint8_t v_v_136_; 
v_v_136_ = lean_ctor_get_uint8(v_val_135_, 0);
lean_dec_ref_known(v_val_135_, 0);
return v_v_136_;
}
else
{
uint8_t v___x_137_; 
lean_dec(v_val_135_);
v___x_137_ = lean_unbox(v_defValue_131_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object* v_opts_138_, lean_object* v_opt_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v_opts_138_, v_opt_139_);
lean_dec_ref(v_opt_139_);
lean_dec_ref(v_opts_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Array_mkArray0___redArg();
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object* v_goal_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_seq_180_; lean_object* v_goal_181_; lean_object* v_seq_184_; lean_object* v___y_186_; uint8_t v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v_mvarId_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v_seq_249_; lean_object* v_goal_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_seq_184_ = lean_box(0);
v___x_294_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_176_);
v___x_295_ = l_Lean_Meta_tactic_hygienic;
v___x_296_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_294_, v___x_295_);
lean_dec_ref(v___x_294_);
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7));
lean_inc_ref(v_goal_168_);
v___x_298_ = l_Lean_Meta_Grind_Goal_intros(v_goal_168_, v___x_297_, v___x_296_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
if (lean_obj_tag(v_a_299_) == 1)
{
lean_object* v_goal_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_goal_168_);
v_goal_300_ = lean_ctor_get(v_a_299_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_299_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_a_299_, 0);
lean_dec(v_unused_329_);
v___x_302_ = v_a_299_;
v_isShared_303_ = v_isSharedCheck_328_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_goal_300_);
lean_dec(v_a_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_328_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_300_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v_ref_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v_ref_306_ = lean_ctor_get(v_a_176_, 2);
v___x_307_ = 0;
v___x_308_ = l_Lean_SourceInfo_fromRef(v_ref_306_, v___x_307_);
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9));
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10));
lean_inc(v___x_308_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 2);
lean_ctor_set(v___x_302_, 1, v___x_310_);
lean_ctor_set(v___x_302_, 0, v___x_308_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_319_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12));
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13);
lean_inc(v___x_308_);
v___x_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_308_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
v___x_316_ = l_Lean_Syntax_node2(v___x_308_, v___x_309_, v___x_312_, v___x_315_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_seq_184_);
v___x_318_ = l_List_appendTR___redArg(v_seq_184_, v___x_317_);
v_seq_249_ = v___x_318_;
v_goal_250_ = v_a_305_;
v___y_251_ = v_a_169_;
v___y_252_ = v_a_170_;
v___y_253_ = v_a_171_;
v___y_254_ = v_a_172_;
v___y_255_ = v_a_173_;
v___y_256_ = v_a_174_;
v___y_257_ = v_a_175_;
v___y_258_ = v_a_176_;
v___y_259_ = v_a_177_;
goto v___jp_248_;
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_del_object(v___x_302_);
v_a_320_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_304_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_304_);
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
else
{
lean_dec(v_a_299_);
v_seq_249_ = v_seq_184_;
v_goal_250_ = v_goal_168_;
v___y_251_ = v_a_169_;
v___y_252_ = v_a_170_;
v___y_253_ = v_a_171_;
v___y_254_ = v_a_172_;
v___y_255_ = v_a_173_;
v___y_256_ = v_a_174_;
v___y_257_ = v_a_175_;
v___y_258_ = v_a_176_;
v___y_259_ = v_a_177_;
goto v___jp_248_;
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_goal_168_);
v_a_330_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_298_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_298_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
v___jp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_seq_180_);
lean_ctor_set(v___x_182_, 1, v_goal_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
v___jp_185_:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_MVarId_byContra_x3f(v_mvarId_190_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
if (lean_obj_tag(v_a_201_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_203_; 
lean_dec_ref(v___y_186_);
v_val_202_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v_a_201_, 1);
v___x_203_ = l_Lean_Meta_intro1Core(v_val_202_, v___y_187_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v_snd_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_230_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_203_, 1);
v_snd_205_ = lean_ctor_get(v_a_204_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_a_204_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v_a_204_, 0);
lean_dec(v_unused_231_);
v___x_207_ = v_a_204_;
v_isShared_208_ = v_isSharedCheck_230_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_snd_205_);
lean_dec(v_a_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_230_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___y_188_);
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___y_188_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_snd_205_);
v___x_210_ = v_reuseFailAlloc_229_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_Goal_internalizeAll(v___x_210_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_ref_213_ = lean_ctor_get(v___y_198_, 2);
v___x_214_ = l_Lean_SourceInfo_fromRef(v_ref_213_, v___y_187_);
v___x_215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5));
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6));
lean_inc(v___x_214_);
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = l_Lean_Syntax_node1(v___x_214_, v___x_215_, v___x_217_);
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_seq_184_);
v___x_220_ = l_List_appendTR___redArg(v___y_189_, v___x_219_);
v_seq_180_ = v___x_220_;
v_goal_181_ = v_a_212_;
goto v___jp_179_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v___y_189_);
v_a_221_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
v_a_232_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_203_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_203_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_dec(v_a_201_);
lean_dec_ref(v___y_188_);
v_seq_180_ = v___y_189_;
v_goal_181_ = v___y_186_;
goto v___jp_179_;
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v___y_186_);
v_a_240_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_200_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_200_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
v___jp_248_:
{
lean_object* v_toGoalState_260_; lean_object* v_mvarId_261_; lean_object* v___x_262_; 
v_toGoalState_260_ = lean_ctor_get(v_goal_250_, 0);
v_mvarId_261_ = lean_ctor_get(v_goal_250_, 1);
lean_inc(v_mvarId_261_);
v___x_262_ = l_Lean_MVarId_getType(v_mvarId_261_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; uint8_t v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = l_Lean_Expr_isFalse(v_a_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_inc_ref(v_toGoalState_260_);
v___x_265_ = l_Lean_Meta_isProp(v_a_263_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; uint8_t v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = lean_unbox(v_a_266_);
lean_dec(v_a_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_inc(v_mvarId_261_);
v___x_268_ = l_Lean_MVarId_exfalso(v_mvarId_261_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___y_186_ = v_goal_250_;
v___y_187_ = v___x_264_;
v___y_188_ = v_toGoalState_260_;
v___y_189_ = v_seq_249_;
v_mvarId_190_ = v_a_269_;
v___y_191_ = v___y_251_;
v___y_192_ = v___y_252_;
v___y_193_ = v___y_253_;
v___y_194_ = v___y_254_;
v___y_195_ = v___y_255_;
v___y_196_ = v___y_256_;
v___y_197_ = v___y_257_;
v___y_198_ = v___y_258_;
v___y_199_ = v___y_259_;
goto v___jp_185_;
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_toGoalState_260_);
lean_dec_ref(v_goal_250_);
lean_dec(v_seq_249_);
v_a_270_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_268_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_inc(v_mvarId_261_);
v___y_186_ = v_goal_250_;
v___y_187_ = v___x_264_;
v___y_188_ = v_toGoalState_260_;
v___y_189_ = v_seq_249_;
v_mvarId_190_ = v_mvarId_261_;
v___y_191_ = v___y_251_;
v___y_192_ = v___y_252_;
v___y_193_ = v___y_253_;
v___y_194_ = v___y_254_;
v___y_195_ = v___y_255_;
v___y_196_ = v___y_256_;
v___y_197_ = v___y_257_;
v___y_198_ = v___y_258_;
v___y_199_ = v___y_259_;
goto v___jp_185_;
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_toGoalState_260_);
lean_dec_ref(v_goal_250_);
lean_dec(v_seq_249_);
v_a_278_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_265_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_265_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_dec(v_a_263_);
v_seq_180_ = v_seq_249_;
v_goal_181_ = v_goal_250_;
goto v___jp_179_;
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_goal_250_);
lean_dec(v_seq_249_);
v_a_286_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_262_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_262_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object* v_goal_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_goal_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
v___x_351_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v___x_388_; lean_object* v_env_389_; lean_object* v___x_390_; lean_object* v_toCold_391_; lean_object* v_mctx_392_; lean_object* v_lctx_393_; lean_object* v_options_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v___x_388_ = 0;
v_env_389_ = l_Lean_Environment_setRecordingDeps(v_env_387_, v___x_388_);
v___x_390_ = lean_st_ref_get(v___y_382_);
v_toCold_391_ = lean_ctor_get(v___y_383_, 0);
v_mctx_392_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_mctx_392_);
lean_dec(v___x_390_);
v_lctx_393_ = lean_ctor_get(v___y_381_, 2);
v_options_394_ = lean_ctor_get(v_toCold_391_, 2);
lean_inc_ref(v_options_394_);
lean_inc_ref(v_lctx_393_);
v___x_395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_395_, 0, v_env_389_);
lean_ctor_set(v___x_395_, 1, v_mctx_392_);
lean_ctor_set(v___x_395_, 2, v_lctx_393_);
lean_ctor_set(v___x_395_, 3, v_options_394_);
v___x_396_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_msgData_380_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object* v_msgData_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msgData_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_ref_411_ = lean_ctor_get(v___y_408_, 2);
v___x_412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_ref_411_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_ref_411_);
lean_ctor_set(v___x_417_, 1, v_a_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 1);
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_436_, lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 1)
{
lean_object* v_pre_438_; 
v_pre_438_ = lean_ctor_get(v_x_437_, 0);
switch(lean_obj_tag(v_pre_438_))
{
case 1:
{
lean_object* v_pre_439_; 
v_pre_439_ = lean_ctor_get(v_pre_438_, 0);
switch(lean_obj_tag(v_pre_439_))
{
case 0:
{
lean_object* v_str_440_; lean_object* v_str_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_str_440_ = lean_ctor_get(v_x_437_, 1);
v_str_441_ = lean_ctor_get(v_pre_438_, 1);
v___x_442_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_443_ = lean_string_dec_eq(v_str_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_445_ = lean_string_dec_eq(v_str_441_, v___x_444_);
if (v___x_445_ == 0)
{
return v___x_445_;
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_447_ = lean_string_dec_eq(v_str_440_, v___x_446_);
if (v___x_447_ == 0)
{
return v___x_447_;
}
else
{
return v_suppressElabErrors_436_;
}
}
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_449_ = lean_string_dec_eq(v_str_440_, v___x_448_);
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
return v_suppressElabErrors_436_;
}
}
}
case 1:
{
lean_object* v_pre_450_; 
v_pre_450_ = lean_ctor_get(v_pre_439_, 0);
if (lean_obj_tag(v_pre_450_) == 0)
{
lean_object* v_str_451_; lean_object* v_str_452_; lean_object* v_str_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_str_451_ = lean_ctor_get(v_x_437_, 1);
v_str_452_ = lean_ctor_get(v_pre_438_, 1);
v_str_453_ = lean_ctor_get(v_pre_439_, 1);
v___x_454_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_455_ = lean_string_dec_eq(v_str_453_, v___x_454_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_457_ = lean_string_dec_eq(v_str_452_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_459_ = lean_string_dec_eq(v_str_451_, v___x_458_);
if (v___x_459_ == 0)
{
return v___x_459_;
}
else
{
return v_suppressElabErrors_436_;
}
}
}
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
default: 
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
case 0:
{
lean_object* v_str_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_str_462_ = lean_ctor_get(v_x_437_, 1);
v___x_463_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_464_ = lean_string_dec_eq(v_str_462_, v___x_463_);
if (v___x_464_ == 0)
{
return v___x_464_;
}
else
{
return v_suppressElabErrors_436_;
}
}
default: 
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
}
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_467_, lean_object* v_x_468_){
_start:
{
uint8_t v_suppressElabErrors_boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v_suppressElabErrors_boxed_469_ = lean_unbox(v_suppressElabErrors_467_);
v_res_470_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_469_, v_x_468_);
lean_dec(v_x_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_473_, lean_object* v_msgData_474_, uint8_t v_severity_475_, uint8_t v_isSilent_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; uint8_t v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v_toCold_490_; lean_object* v___y_491_; lean_object* v___y_520_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; uint8_t v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; uint8_t v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v___y_557_; uint8_t v___y_558_; uint8_t v___x_568_; uint8_t v___y_570_; uint8_t v___x_576_; 
v___x_568_ = 2;
v___x_576_ = l_Lean_instBEqMessageSeverity_beq(v_severity_475_, v___x_568_);
if (v___x_576_ == 0)
{
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
else
{
uint8_t v___x_577_; 
lean_inc_ref(v_msgData_474_);
v___x_577_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_474_);
if (v___x_577_ == 0)
{
v___y_570_ = v___x_577_;
goto v___jp_569_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_msgData_474_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
v___jp_482_:
{
lean_object* v_currNamespace_492_; lean_object* v_openDecls_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_env_498_; lean_object* v_nextMacroScope_499_; lean_object* v_ngen_500_; lean_object* v_auxDeclNGen_501_; lean_object* v_traceState_502_; lean_object* v_cache_503_; lean_object* v_recordedDeps_504_; lean_object* v_messages_505_; lean_object* v_infoState_506_; lean_object* v_snapshotTasks_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_518_; 
v_currNamespace_492_ = lean_ctor_get(v_toCold_490_, 4);
v_openDecls_493_ = lean_ctor_get(v_toCold_490_, 5);
lean_inc(v_openDecls_493_);
lean_inc(v_currNamespace_492_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_currNamespace_492_);
lean_ctor_set(v___x_494_, 1, v_openDecls_493_);
v___x_495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___y_488_);
lean_inc_ref(v___y_484_);
lean_inc_ref(v___y_487_);
v___x_496_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_496_, 0, v___y_487_);
lean_ctor_set(v___x_496_, 1, v___y_483_);
lean_ctor_set(v___x_496_, 2, v___y_489_);
lean_ctor_set(v___x_496_, 3, v___y_484_);
lean_ctor_set(v___x_496_, 4, v___x_495_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*5, v___y_486_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*5 + 1, v___y_485_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*5 + 2, v_isSilent_476_);
v___x_497_ = lean_st_ref_take(v___y_491_);
v_env_498_ = lean_ctor_get(v___x_497_, 0);
v_nextMacroScope_499_ = lean_ctor_get(v___x_497_, 1);
v_ngen_500_ = lean_ctor_get(v___x_497_, 2);
v_auxDeclNGen_501_ = lean_ctor_get(v___x_497_, 3);
v_traceState_502_ = lean_ctor_get(v___x_497_, 4);
v_cache_503_ = lean_ctor_get(v___x_497_, 5);
v_recordedDeps_504_ = lean_ctor_get(v___x_497_, 6);
v_messages_505_ = lean_ctor_get(v___x_497_, 7);
v_infoState_506_ = lean_ctor_get(v___x_497_, 8);
v_snapshotTasks_507_ = lean_ctor_get(v___x_497_, 9);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_518_ == 0)
{
v___x_509_ = v___x_497_;
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snapshotTasks_507_);
lean_inc(v_infoState_506_);
lean_inc(v_messages_505_);
lean_inc(v_recordedDeps_504_);
lean_inc(v_cache_503_);
lean_inc(v_traceState_502_);
lean_inc(v_auxDeclNGen_501_);
lean_inc(v_ngen_500_);
lean_inc(v_nextMacroScope_499_);
lean_inc(v_env_498_);
lean_dec(v___x_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_511_ = lean_box(0);
v___x_512_ = l_Lean_MessageLog_add(v___x_496_, v_messages_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 7, v___x_512_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_env_498_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_nextMacroScope_499_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_ngen_500_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_auxDeclNGen_501_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_traceState_502_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v_cache_503_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_recordedDeps_504_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_infoState_506_);
lean_ctor_set(v_reuseFailAlloc_517_, 9, v_snapshotTasks_507_);
v___x_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_st_ref_put(v___y_491_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_511_);
return v___x_516_;
}
}
}
v___jp_519_:
{
lean_object* v_fileName_528_; lean_object* v_fileMap_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_545_; 
v_fileName_528_ = lean_ctor_get(v___y_526_, 0);
v_fileMap_529_ = lean_ctor_get(v___y_526_, 1);
v___x_530_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_474_);
v___x_531_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v___x_530_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_545_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_545_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_545_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_inc_ref_n(v_fileMap_529_, 2);
v___x_536_ = l_Lean_FileMap_toPosition(v_fileMap_529_, v___y_523_);
lean_dec(v___y_523_);
v___x_537_ = l_Lean_FileMap_toPosition(v_fileMap_529_, v___y_527_);
lean_dec(v___y_527_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0));
if (v___y_522_ == 0)
{
lean_del_object(v___x_534_);
lean_dec_ref(v___y_520_);
v___y_483_ = v___x_536_;
v___y_484_ = v___x_539_;
v___y_485_ = v___y_525_;
v___y_486_ = v___y_524_;
v___y_487_ = v_fileName_528_;
v___y_488_ = v_a_532_;
v___y_489_ = v___x_538_;
v_toCold_490_ = v___y_521_;
v___y_491_ = v___y_480_;
goto v___jp_482_;
}
else
{
uint8_t v___x_540_; 
lean_inc(v_a_532_);
v___x_540_ = l_Lean_MessageData_hasTag(v___y_520_, v_a_532_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec_ref_known(v___x_538_, 1);
lean_dec_ref(v___x_536_);
lean_dec(v_a_532_);
v___x_541_ = lean_box(0);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_541_);
v___x_543_ = v___x_534_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_del_object(v___x_534_);
v___y_483_ = v___x_536_;
v___y_484_ = v___x_539_;
v___y_485_ = v___y_525_;
v___y_486_ = v___y_524_;
v___y_487_ = v_fileName_528_;
v___y_488_ = v_a_532_;
v___y_489_ = v___x_538_;
v_toCold_490_ = v___y_521_;
v___y_491_ = v___y_480_;
goto v___jp_482_;
}
}
}
}
v___jp_546_:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Syntax_getTailPos_x3f(v___y_552_, v___y_551_);
lean_dec(v___y_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_inc(v___y_553_);
v___y_520_ = v___y_548_;
v___y_521_ = v___y_549_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_553_;
v___y_524_ = v___y_551_;
v___y_525_ = v___y_550_;
v___y_526_ = v___y_549_;
v___y_527_ = v___y_553_;
goto v___jp_519_;
}
else
{
lean_object* v_val_555_; 
v_val_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v___x_554_, 1);
v___y_520_ = v___y_548_;
v___y_521_ = v___y_549_;
v___y_522_ = v___y_547_;
v___y_523_ = v___y_553_;
v___y_524_ = v___y_551_;
v___y_525_ = v___y_550_;
v___y_526_ = v___y_549_;
v___y_527_ = v_val_555_;
goto v___jp_519_;
}
}
v___jp_556_:
{
lean_object* v_toCold_559_; lean_object* v_ref_560_; uint8_t v_suppressElabErrors_561_; lean_object* v___x_562_; lean_object* v___f_563_; lean_object* v_ref_564_; lean_object* v___x_565_; 
v_toCold_559_ = lean_ctor_get(v___y_479_, 0);
v_ref_560_ = lean_ctor_get(v___y_479_, 2);
v_suppressElabErrors_561_ = lean_ctor_get_uint8(v___y_479_, sizeof(void*)*3 + 2);
v___x_562_ = lean_box(v_suppressElabErrors_561_);
v___f_563_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_563_, 0, v___x_562_);
v_ref_564_ = l_Lean_replaceRef(v_ref_473_, v_ref_560_);
v___x_565_ = l_Lean_Syntax_getPos_x3f(v_ref_564_, v___y_557_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___y_547_ = v_suppressElabErrors_561_;
v___y_548_ = v___f_563_;
v___y_549_ = v_toCold_559_;
v___y_550_ = v___y_558_;
v___y_551_ = v___y_557_;
v___y_552_ = v_ref_564_;
v___y_553_ = v___x_566_;
goto v___jp_546_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_565_, 1);
v___y_547_ = v_suppressElabErrors_561_;
v___y_548_ = v___f_563_;
v___y_549_ = v_toCold_559_;
v___y_550_ = v___y_558_;
v___y_551_ = v___y_557_;
v___y_552_ = v_ref_564_;
v___y_553_ = v_val_567_;
goto v___jp_546_;
}
}
v___jp_569_:
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 1;
v___x_572_ = l_Lean_instBEqMessageSeverity_beq(v_severity_475_, v___x_571_);
if (v___x_572_ == 0)
{
v___y_557_ = v___y_570_;
v___y_558_ = v_severity_475_;
goto v___jp_556_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_479_);
v___x_574_ = l_Lean_warningAsError;
v___x_575_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_573_, v___x_574_);
lean_dec_ref(v___x_573_);
if (v___x_575_ == 0)
{
v___y_557_ = v___y_570_;
v___y_558_ = v_severity_475_;
goto v___jp_556_;
}
else
{
v___y_557_ = v___y_570_;
v___y_558_ = v___x_568_;
goto v___jp_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_580_, lean_object* v_msgData_581_, lean_object* v_severity_582_, lean_object* v_isSilent_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v_severity_boxed_589_; uint8_t v_isSilent_boxed_590_; lean_object* v_res_591_; 
v_severity_boxed_589_ = lean_unbox(v_severity_582_);
v_isSilent_boxed_590_ = lean_unbox(v_isSilent_583_);
v_res_591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_580_, v_msgData_581_, v_severity_boxed_589_, v_isSilent_boxed_590_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v_ref_580_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_592_, uint8_t v_severity_593_, uint8_t v_isSilent_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_ref_605_; lean_object* v___x_606_; 
v_ref_605_ = lean_ctor_get(v___y_602_, 2);
v___x_606_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_605_, v_msgData_592_, v_severity_593_, v_isSilent_594_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_607_, lean_object* v_severity_608_, lean_object* v_isSilent_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v_severity_boxed_620_; uint8_t v_isSilent_boxed_621_; lean_object* v_res_622_; 
v_severity_boxed_620_ = lean_unbox(v_severity_608_);
v_isSilent_boxed_621_ = lean_unbox(v_isSilent_609_);
v_res_622_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_607_, v_severity_boxed_620_, v_isSilent_boxed_621_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_msgData_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_634_ = 1;
v___x_635_ = 0;
v___x_636_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_623_, v___x_634_, v___x_635_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_msgData_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_msgData_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v___x_667_, lean_object* v_stx_668_, uint8_t v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v___x_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v_a_679_, lean_object* v_params_680_, lean_object* v_____x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_suggestions_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_907_; 
v_fst_743_ = lean_ctor_get(v_____x_681_, 0);
v_snd_744_ = lean_ctor_get(v_____x_681_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_____x_681_);
if (v_isSharedCheck_907_ == 0)
{
v___x_746_ = v_____x_681_;
v_isShared_747_ = v_isSharedCheck_907_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v_____x_681_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_907_;
goto v_resetjp_745_;
}
v___jp_692_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_array_get_size(v_suggestions_693_);
v___x_697_ = lean_nat_dec_eq(v___x_696_, v___x_667_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_698_ = lean_box(0);
v___x_699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_700_ = 4;
v___x_701_ = l_Lean_MessageData_nil;
v___x_702_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_668_, v_suggestions_693_, v___x_698_, v___x_699_, v___x_698_, v___x_700_, v___x_701_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_711_);
v___x_704_ = v___x_702_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_702_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_box(v___x_669_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_712_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_702_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_702_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_720_ = lean_array_get(v___x_670_, v_suggestions_693_, v___x_671_);
lean_dec_ref(v_suggestions_693_);
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_723_ = 4;
v___x_724_ = l_Lean_MessageData_nil;
v___x_725_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_668_, v___x_720_, v___x_721_, v___x_722_, v___x_721_, v___x_723_, v___x_724_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_734_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_box(v___x_669_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_725_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_725_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
v_resetjp_745_:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_Grind_Action_run(v_snd_744_, v_a_672_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
if (lean_obj_tag(v_a_749_) == 0)
{
lean_object* v_seq_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_857_; 
v_seq_750_ = lean_ctor_get(v_a_749_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_a_749_);
if (v_isSharedCheck_857_ == 0)
{
v___x_752_ = v_a_749_;
v_isShared_753_ = v_isSharedCheck_857_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_seq_750_);
lean_dec(v_a_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_857_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_List_appendTR___redArg(v_fst_743_, v_seq_750_);
lean_inc(v___x_754_);
v___x_755_ = l_Lean_Meta_Grind_mkFinishTactic(v___x_754_, v_a_673_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v_suggestions_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_suggestions_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___x_840_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
lean_inc_n(v___x_754_, 2);
v___x_757_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v___x_754_);
v___x_817_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_a_679_);
lean_inc_ref(v_a_674_);
lean_inc_ref(v___x_818_);
v___x_840_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_818_, v_a_674_, v___x_754_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
v_suggestions_820_ = v___x_817_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
v___y_823_ = v___y_684_;
v___y_824_ = v___y_685_;
v___y_825_ = v___y_686_;
v___y_826_ = v___y_687_;
v___y_827_ = v___y_688_;
v___y_828_ = v___y_689_;
v___y_829_ = v___y_690_;
goto v___jp_819_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
lean_inc_ref(v___x_678_);
lean_inc_ref(v___x_677_);
lean_inc_ref(v___x_676_);
lean_inc_ref(v___x_675_);
v___x_844_ = l_Lean_Name_mkStr5(v___x_675_, v___x_676_, v___x_677_, v___x_678_, v___x_843_);
lean_inc(v___x_757_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_757_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
lean_ctor_set(v___x_847_, 4, v___x_846_);
lean_ctor_set(v___x_847_, 5, v___x_846_);
v___x_848_ = lean_array_push(v___x_817_, v___x_847_);
v_suggestions_820_ = v___x_848_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
v___y_823_ = v___y_684_;
v___y_824_ = v___y_685_;
v___y_825_ = v___y_686_;
v___y_826_ = v___y_687_;
v___y_827_ = v___y_688_;
v___y_828_ = v___y_689_;
v___y_829_ = v___y_690_;
goto v___jp_819_;
}
}
else
{
lean_dec_ref_known(v___x_818_, 1);
lean_dec_ref(v___x_817_);
lean_dec(v___x_757_);
lean_dec(v_a_756_);
lean_dec(v___x_754_);
lean_del_object(v___x_752_);
lean_del_object(v___x_746_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
return v___x_840_;
}
v___jp_758_:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_suggestions_759_);
v___x_770_ = lean_nat_dec_eq(v___x_769_, v___x_671_);
if (v___x_770_ == 0)
{
lean_dec(v___x_757_);
lean_dec(v___x_754_);
lean_del_object(v___x_752_);
lean_del_object(v___x_746_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
v_suggestions_693_ = v_suggestions_759_;
v___y_694_ = v___y_767_;
v___y_695_ = v___y_768_;
goto v___jp_692_;
}
else
{
lean_object* v___x_771_; 
lean_dec_ref(v_suggestions_759_);
v___x_771_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v___x_754_, v___y_767_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v_mvarId_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_807_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v_mvarId_773_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_a_674_, 0);
lean_dec(v_unused_808_);
v___x_775_ = v_a_674_;
v_isShared_776_ = v_isSharedCheck_807_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_mvarId_773_);
lean_dec(v_a_674_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_807_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3);
v___x_778_ = l_Lean_MessageData_ofSyntax(v_a_772_);
v___x_779_ = l_Lean_indentD(v___x_778_);
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 7);
lean_ctor_set(v___x_775_, 1, v___x_779_);
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_806_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 7);
lean_ctor_set(v___x_746_, 1, v___x_782_);
lean_ctor_set(v___x_746_, 0, v___x_781_);
v___x_784_ = v___x_746_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_805_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v_mvarId_773_);
v___x_786_ = v___x_752_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_mvarId_773_);
v___x_786_ = v_reuseFailAlloc_804_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_784_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v___x_787_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref_known(v___x_788_, 1);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
v___x_790_ = l_Lean_Name_mkStr5(v___x_675_, v___x_676_, v___x_677_, v___x_678_, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_757_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
lean_ctor_set(v___x_793_, 4, v___x_792_);
lean_ctor_set(v___x_793_, 5, v___x_792_);
v___x_794_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_795_ = lean_array_push(v___x_794_, v___x_793_);
v_suggestions_693_ = v___x_795_;
v___y_694_ = v___y_767_;
v___y_695_ = v___y_768_;
goto v___jp_692_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v___x_757_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec(v_stx_668_);
v_a_796_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_788_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_788_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
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
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v___x_757_);
lean_del_object(v___x_752_);
lean_del_object(v___x_746_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
v_a_809_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_771_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_771_);
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
v___jp_819_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
lean_inc(v_a_756_);
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v_a_756_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_inc_ref(v_a_674_);
v___x_832_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_818_, v_a_674_, v___x_831_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; uint8_t v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
if (v___x_834_ == 0)
{
lean_dec(v_a_756_);
v_suggestions_759_ = v_suggestions_820_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
v___y_762_ = v___y_823_;
v___y_763_ = v___y_824_;
v___y_764_ = v___y_825_;
v___y_765_ = v___y_826_;
v___y_766_ = v___y_827_;
v___y_767_ = v___y_828_;
v___y_768_ = v___y_829_;
goto v___jp_758_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8));
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_a_756_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
lean_ctor_set(v___x_838_, 2, v___x_837_);
lean_ctor_set(v___x_838_, 3, v___x_837_);
lean_ctor_set(v___x_838_, 4, v___x_837_);
lean_ctor_set(v___x_838_, 5, v___x_837_);
v___x_839_ = lean_array_push(v_suggestions_820_, v___x_838_);
v_suggestions_759_ = v___x_839_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
v___y_762_ = v___y_823_;
v___y_763_ = v___y_824_;
v___y_764_ = v___y_825_;
v___y_765_ = v___y_826_;
v___y_766_ = v___y_827_;
v___y_767_ = v___y_828_;
v___y_768_ = v___y_829_;
goto v___jp_758_;
}
}
else
{
lean_dec_ref(v_suggestions_820_);
lean_dec(v___x_757_);
lean_dec(v_a_756_);
lean_dec(v___x_754_);
lean_del_object(v___x_752_);
lean_del_object(v___x_746_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
return v___x_832_;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v___x_754_);
lean_del_object(v___x_752_);
lean_del_object(v___x_746_);
lean_dec_ref(v_a_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
v_a_849_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_755_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_755_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
else
{
lean_object* v_gs_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_746_);
lean_dec(v_fst_743_);
lean_dec_ref(v_a_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
v_gs_858_ = lean_ctor_get(v_a_749_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_749_);
if (v_isSharedCheck_898_ == 0)
{
v___x_860_ = v_a_749_;
v_isShared_861_ = v_isSharedCheck_898_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_gs_858_);
lean_dec(v_a_749_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_898_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
if (lean_obj_tag(v_gs_858_) == 1)
{
lean_object* v_head_862_; lean_object* v___x_864_; 
v_head_862_ = lean_ctor_get(v_gs_858_, 0);
lean_inc(v_head_862_);
lean_dec_ref_known(v_gs_858_, 2);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v_head_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_head_862_);
v___x_864_ = v_reuseFailAlloc_895_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Grind_mkResult(v_params_680_, v___x_864_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10));
v___x_868_ = l_Lean_Meta_Grind_Result_toErrorMessageData(v_a_866_, v___x_867_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_a_869_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_868_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_868_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_865_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_865_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_del_object(v___x_860_);
lean_dec(v_gs_858_);
v___x_896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12);
v___x_897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_896_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_746_);
lean_dec(v_fst_743_);
lean_dec_ref(v_a_679_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_stx_668_);
v_a_899_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_748_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_748_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v___x_908_ = _args[0];
lean_object* v_stx_909_ = _args[1];
lean_object* v___x_910_ = _args[2];
lean_object* v___x_911_ = _args[3];
lean_object* v___x_912_ = _args[4];
lean_object* v_a_913_ = _args[5];
lean_object* v_a_914_ = _args[6];
lean_object* v_a_915_ = _args[7];
lean_object* v___x_916_ = _args[8];
lean_object* v___x_917_ = _args[9];
lean_object* v___x_918_ = _args[10];
lean_object* v___x_919_ = _args[11];
lean_object* v_a_920_ = _args[12];
lean_object* v_params_921_ = _args[13];
lean_object* v_____x_922_ = _args[14];
lean_object* v___y_923_ = _args[15];
lean_object* v___y_924_ = _args[16];
lean_object* v___y_925_ = _args[17];
lean_object* v___y_926_ = _args[18];
lean_object* v___y_927_ = _args[19];
lean_object* v___y_928_ = _args[20];
lean_object* v___y_929_ = _args[21];
lean_object* v___y_930_ = _args[22];
lean_object* v___y_931_ = _args[23];
lean_object* v___y_932_ = _args[24];
_start:
{
uint8_t v___x_49477__boxed_933_; lean_object* v_res_934_; 
v___x_49477__boxed_933_ = lean_unbox(v___x_910_);
v_res_934_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v___x_908_, v_stx_909_, v___x_49477__boxed_933_, v___x_911_, v___x_912_, v_a_913_, v_a_914_, v_a_915_, v___x_916_, v___x_917_, v___x_918_, v___x_919_, v_a_920_, v_params_921_, v_____x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v_params_921_);
lean_dec_ref(v_a_914_);
lean_dec(v___x_912_);
lean_dec_ref(v___x_911_);
lean_dec(v___x_908_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t v_sym_935_, lean_object* v_a_936_, lean_object* v___f_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
if (v_sym_935_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_a_936_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
lean_inc(v___y_938_);
v___x_950_ = lean_apply_11(v___f_937_, v___x_949_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, lean_box(0));
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_a_936_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
lean_inc(v___y_938_);
v___x_953_ = lean_apply_11(v___f_937_, v_a_952_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, lean_box(0));
return v___x_953_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___f_937_);
v_a_954_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_951_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_951_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v_sym_962_, lean_object* v_a_963_, lean_object* v___f_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v_sym_boxed_975_; lean_object* v_res_976_; 
v_sym_boxed_975_ = lean_unbox(v_sym_962_);
v_res_976_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v_sym_boxed_975_, v_a_963_, v___f_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___y_977_, v___y_978_, v___y_979_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_999_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_999_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
uint8_t v___x_992_; 
v___x_992_ = lean_unbox(v_a_988_);
lean_dec(v_a_988_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_990_);
v___x_997_ = lean_box(0);
v___x_998_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_997_, v___y_979_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_987_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_987_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v_stx_1021_, uint8_t v___x_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_a_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_ref_1041_; lean_object* v___x_1042_; 
v_ref_1041_ = lean_ctor_get(v___y_1038_, 2);
v___x_1042_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1019_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1033_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v_params_1046_; uint8_t v_sym_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___y_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v_params_1046_ = lean_ctor_get(v___y_1032_, 4);
v_sym_1047_ = lean_ctor_get_uint8(v___y_1032_, sizeof(void*)*5);
v___x_1048_ = lean_box(v___x_1022_);
lean_inc_ref(v_params_1046_);
v___f_1049_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 25, 14);
lean_closure_set(v___f_1049_, 0, v___x_1020_);
lean_closure_set(v___f_1049_, 1, v_stx_1021_);
lean_closure_set(v___f_1049_, 2, v___x_1048_);
lean_closure_set(v___f_1049_, 3, v___x_1023_);
lean_closure_set(v___f_1049_, 4, v___x_1024_);
lean_closure_set(v___f_1049_, 5, v_a_1043_);
lean_closure_set(v___f_1049_, 6, v_a_1025_);
lean_closure_set(v___f_1049_, 7, v_a_1026_);
lean_closure_set(v___f_1049_, 8, v___x_1027_);
lean_closure_set(v___f_1049_, 9, v___x_1028_);
lean_closure_set(v___f_1049_, 10, v___x_1029_);
lean_closure_set(v___f_1049_, 11, v___x_1030_);
lean_closure_set(v___f_1049_, 12, v_a_1031_);
lean_closure_set(v___f_1049_, 13, v_params_1046_);
v___x_1050_ = lean_box(v_sym_1047_);
v___y_1051_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 13, 3);
lean_closure_set(v___y_1051_, 0, v___x_1050_);
lean_closure_set(v___y_1051_, 1, v_a_1045_);
lean_closure_set(v___y_1051_, 2, v___f_1049_);
v___f_1052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1052_, 0, v___y_1051_);
v___x_1053_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1052_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec_ref(v___y_1032_);
return v___x_1053_;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_a_1043_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v___x_1024_);
lean_dec_ref(v___x_1023_);
lean_dec(v_stx_1021_);
lean_dec(v___x_1020_);
v_a_1054_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1044_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1044_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v___x_1024_);
lean_dec_ref(v___x_1023_);
lean_dec(v_stx_1021_);
lean_dec(v___x_1020_);
v_a_1062_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1064_ = v___x_1042_;
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1042_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1066_ = lean_io_error_to_string(v_a_1062_);
v___x_1067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
v___x_1068_ = l_Lean_MessageData_ofFormat(v___x_1067_);
lean_inc(v_ref_1041_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_ref_1041_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1069_);
v___x_1071_ = v___x_1064_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___x_1074_ = _args[0];
lean_object* v___x_1075_ = _args[1];
lean_object* v_stx_1076_ = _args[2];
lean_object* v___x_1077_ = _args[3];
lean_object* v___x_1078_ = _args[4];
lean_object* v___x_1079_ = _args[5];
lean_object* v_a_1080_ = _args[6];
lean_object* v_a_1081_ = _args[7];
lean_object* v___x_1082_ = _args[8];
lean_object* v___x_1083_ = _args[9];
lean_object* v___x_1084_ = _args[10];
lean_object* v___x_1085_ = _args[11];
lean_object* v_a_1086_ = _args[12];
lean_object* v___y_1087_ = _args[13];
lean_object* v___y_1088_ = _args[14];
lean_object* v___y_1089_ = _args[15];
lean_object* v___y_1090_ = _args[16];
lean_object* v___y_1091_ = _args[17];
lean_object* v___y_1092_ = _args[18];
lean_object* v___y_1093_ = _args[19];
lean_object* v___y_1094_ = _args[20];
lean_object* v___y_1095_ = _args[21];
_start:
{
uint8_t v___x_50132__boxed_1096_; lean_object* v_res_1097_; 
v___x_50132__boxed_1096_ = lean_unbox(v___x_1077_);
v_res_1097_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___x_1074_, v___x_1075_, v_stx_1076_, v___x_50132__boxed_1096_, v___x_1078_, v___x_1079_, v_a_1080_, v_a_1081_, v___x_1082_, v___x_1083_, v___x_1084_, v___x_1085_, v_a_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v_stx_1101_, uint8_t v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v_only_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v___x_1099_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1111_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0));
v___x_1124_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1123_, v___y_1110_, v___y_1111_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v_params_1126_; uint8_t v___y_1128_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v_params_1126_ = lean_ctor_get(v___y_1110_, 4);
lean_inc_ref(v_params_1126_);
if (lean_obj_tag(v_only_1109_) == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
v___y_1128_ = v___x_1133_;
goto v___jp_1127_;
}
else
{
v___y_1128_ = v___x_1102_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_unsigned_to_nat(10000u);
v___x_1130_ = lean_box(v___x_1102_);
v___f_1131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 22, 13);
lean_closure_set(v___f_1131_, 0, v___x_1129_);
lean_closure_set(v___f_1131_, 1, v___x_1100_);
lean_closure_set(v___f_1131_, 2, v_stx_1101_);
lean_closure_set(v___f_1131_, 3, v___x_1130_);
lean_closure_set(v___f_1131_, 4, v___x_1103_);
lean_closure_set(v___f_1131_, 5, v___x_1104_);
lean_closure_set(v___f_1131_, 6, v_a_1120_);
lean_closure_set(v___f_1131_, 7, v_a_1122_);
lean_closure_set(v___f_1131_, 8, v___x_1105_);
lean_closure_set(v___f_1131_, 9, v___x_1106_);
lean_closure_set(v___f_1131_, 10, v___x_1107_);
lean_closure_set(v___f_1131_, 11, v___x_1108_);
lean_closure_set(v___f_1131_, 12, v_a_1125_);
v___x_1132_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_1126_, v___x_1099_, v___y_1128_, v___f_1131_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec_ref(v___y_1110_);
return v___x_1132_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_a_1122_);
lean_dec(v_a_1120_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v_stx_1101_);
lean_dec(v___x_1100_);
v_a_1134_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_1120_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v_stx_1101_);
lean_dec(v___x_1100_);
v_a_1142_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1121_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1121_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v_stx_1101_);
lean_dec(v___x_1100_);
v_a_1150_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1119_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1119_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object** _args){
lean_object* v___x_1158_ = _args[0];
lean_object* v___x_1159_ = _args[1];
lean_object* v_stx_1160_ = _args[2];
lean_object* v___x_1161_ = _args[3];
lean_object* v___x_1162_ = _args[4];
lean_object* v___x_1163_ = _args[5];
lean_object* v___x_1164_ = _args[6];
lean_object* v___x_1165_ = _args[7];
lean_object* v___x_1166_ = _args[8];
lean_object* v___x_1167_ = _args[9];
lean_object* v_only_1168_ = _args[10];
lean_object* v___y_1169_ = _args[11];
lean_object* v___y_1170_ = _args[12];
lean_object* v___y_1171_ = _args[13];
lean_object* v___y_1172_ = _args[14];
lean_object* v___y_1173_ = _args[15];
lean_object* v___y_1174_ = _args[16];
lean_object* v___y_1175_ = _args[17];
lean_object* v___y_1176_ = _args[18];
lean_object* v___y_1177_ = _args[19];
_start:
{
uint8_t v___x_50257__boxed_1178_; lean_object* v_res_1179_; 
v___x_50257__boxed_1178_ = lean_unbox(v___x_1161_);
v_res_1179_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(v___x_1158_, v___x_1159_, v_stx_1160_, v___x_50257__boxed_1178_, v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_, v___x_1166_, v___x_1167_, v_only_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec(v_only_1168_);
lean_dec_ref(v___x_1158_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_1180_, size_t v_i_1181_, lean_object* v_bs_1182_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1181_, v_sz_1180_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_bs_1182_);
return v___x_1184_;
}
else
{
lean_object* v_v_1185_; lean_object* v___x_1186_; lean_object* v_bs_x27_1187_; size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; 
v_v_1185_ = lean_array_uget(v_bs_1182_, v_i_1181_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v_bs_x27_1187_ = lean_array_uset(v_bs_1182_, v_i_1181_, v___x_1186_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_add(v_i_1181_, v___x_1188_);
v___x_1190_ = lean_array_uset(v_bs_x27_1187_, v_i_1181_, v_v_1185_);
v_i_1181_ = v___x_1189_;
v_bs_1182_ = v___x_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_){
_start:
{
size_t v_sz_boxed_1195_; size_t v_i_boxed_1196_; lean_object* v_res_1197_; 
v_sz_boxed_1195_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1196_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1195_, v_i_boxed_1196_, v_bs_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0));
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1));
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3));
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
lean_inc(v_stx_1207_);
v___x_1222_ = l_Lean_Syntax_isOfKind(v_stx_1207_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec(v_stx_1207_);
v___x_1223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; size_t v_sz_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = l_Lean_Syntax_getArg(v_stx_1207_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_getArgs(v___x_1225_);
lean_dec(v___x_1225_);
v_sz_1227_ = lean_array_size(v___x_1226_);
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1227_, v___x_1228_, v___x_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
lean_dec(v_stx_1207_);
v___x_1230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1280_; 
v_val_1231_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1233_ = v___x_1229_;
v_isShared_1234_ = v_isSharedCheck_1280_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_dec(v___x_1229_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1280_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v_only_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1235_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_unsigned_to_nat(2u);
v___x_1271_ = l_Lean_Syntax_getArg(v_stx_1207_, v___x_1270_);
v___x_1272_ = l_Lean_Syntax_isNone(v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
lean_inc(v___x_1271_);
v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1271_, v___x_1224_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec(v___x_1271_);
lean_del_object(v___x_1233_);
lean_dec(v_val_1231_);
lean_dec(v_stx_1207_);
v___x_1274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1274_;
}
else
{
lean_object* v_only_1275_; lean_object* v___x_1277_; 
v_only_1275_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1236_);
lean_dec(v___x_1271_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_only_1275_);
v___x_1277_ = v___x_1233_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_only_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v_only_1253_ = v___x_1277_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
goto v___jp_1252_;
}
}
}
else
{
lean_object* v___x_1279_; 
lean_dec(v___x_1271_);
lean_del_object(v___x_1233_);
v___x_1279_ = lean_box(0);
v_only_1253_ = v___x_1279_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
goto v___jp_1252_;
}
v___jp_1237_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; 
v___x_1248_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1247_);
lean_dec_ref(v___y_1247_);
v___x_1249_ = lean_box(v___x_1222_);
v___f_1250_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1250_, 0, v___x_1248_);
lean_closure_set(v___f_1250_, 1, v___x_1224_);
lean_closure_set(v___f_1250_, 2, v_stx_1207_);
lean_closure_set(v___f_1250_, 3, v___x_1249_);
lean_closure_set(v___f_1250_, 4, v___x_1235_);
lean_closure_set(v___f_1250_, 5, v___x_1236_);
lean_closure_set(v___f_1250_, 6, v___x_1217_);
lean_closure_set(v___f_1250_, 7, v___x_1218_);
lean_closure_set(v___f_1250_, 8, v___x_1219_);
lean_closure_set(v___f_1250_, 9, v___x_1220_);
lean_closure_set(v___f_1250_, 10, v___y_1238_);
v___x_1251_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_1231_, v___f_1250_, v___y_1242_, v___y_1246_, v___y_1244_, v___y_1239_, v___y_1240_, v___y_1243_, v___y_1241_, v___y_1245_);
return v___x_1251_;
}
v___jp_1252_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(3u);
v___x_1263_ = l_Lean_Syntax_getArg(v_stx_1207_, v___x_1262_);
v___x_1264_ = l_Lean_Syntax_isNone(v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; 
lean_inc(v___x_1263_);
v___x_1265_ = l_Lean_Syntax_matchesNull(v___x_1263_, v___x_1262_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_dec(v___x_1263_);
lean_dec(v_only_1253_);
lean_dec(v_val_1231_);
lean_dec(v_stx_1207_);
v___x_1266_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v_params_x3f_1268_; 
v___x_1267_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_1224_);
lean_dec(v___x_1263_);
v_params_x3f_1268_ = l_Lean_Syntax_getArgs(v___x_1267_);
lean_dec(v___x_1267_);
v___y_1238_ = v_only_1253_;
v___y_1239_ = v___y_1257_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___y_1260_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1261_;
v___y_1246_ = v___y_1255_;
v___y_1247_ = v_params_x3f_1268_;
goto v___jp_1237_;
}
}
else
{
lean_object* v___x_1269_; 
lean_dec(v___x_1263_);
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___y_1238_ = v_only_1253_;
v___y_1239_ = v___y_1257_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___y_1260_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1261_;
v___y_1246_ = v___y_1255_;
v___y_1247_ = v___x_1269_;
goto v___jp_1237_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object* v_00_u03b1_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_1293_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(v_00_u03b1_1305_, v_msg_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object* v_ref_1318_, lean_object* v_msgData_1319_, uint8_t v_severity_1320_, uint8_t v_isSilent_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_1318_, v_msgData_1319_, v_severity_1320_, v_isSilent_1321_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1333_, lean_object* v_msgData_1334_, lean_object* v_severity_1335_, lean_object* v_isSilent_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v_severity_boxed_1347_; uint8_t v_isSilent_boxed_1348_; lean_object* v_res_1349_; 
v_severity_boxed_1347_ = lean_unbox(v_severity_1335_);
v_isSilent_boxed_1348_ = lean_unbox(v_isSilent_1336_);
v_res_1349_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(v_ref_1333_, v_msgData_1334_, v_severity_boxed_1347_, v_isSilent_boxed_1348_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v_ref_1333_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1390_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_1392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14));
v___x_1393_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_1394_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_1396_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Trace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
}
#ifdef __cplusplus
}
#endif
