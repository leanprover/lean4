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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`finish\?` failed\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10;
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
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_symSimpMethods_20_; lean_object* v_symDSimpMethods_21_; lean_object* v_anchorRefs_x3f_22_; uint8_t v_cheapCases_23_; uint8_t v_reportMVarIssue_24_; lean_object* v_splitSource_25_; lean_object* v_ematchDiagSource_26_; lean_object* v_symPrios_27_; lean_object* v_extensions_28_; uint8_t v_debug_29_; uint8_t v_ematchDiag_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_genLocal_38_; lean_object* v_instances_39_; uint8_t v_matchEqs_40_; uint8_t v_splitMatch_41_; uint8_t v_splitIte_42_; uint8_t v_splitIndPred_43_; uint8_t v_splitImp_44_; lean_object* v_canonHeartbeats_45_; uint8_t v_ext_46_; uint8_t v_extAll_47_; uint8_t v_etaStruct_48_; uint8_t v_funext_49_; uint8_t v_lookahead_50_; uint8_t v_verbose_51_; uint8_t v_clean_52_; uint8_t v_qlia_53_; uint8_t v_mbtc_54_; uint8_t v_zetaDelta_55_; uint8_t v_zeta_56_; uint8_t v_distrib_57_; uint8_t v_ring_58_; lean_object* v_ringSteps_59_; lean_object* v_ringMaxDegree_60_; uint8_t v_linarith_61_; uint8_t v_lia_62_; lean_object* v_liaSteps_63_; uint8_t v_hom_64_; uint8_t v_ac_65_; lean_object* v_acSteps_66_; lean_object* v_exp_67_; uint8_t v_abstractProof_68_; uint8_t v_inj_69_; uint8_t v_order_70_; lean_object* v_min_71_; lean_object* v_detailed_72_; uint8_t v_useSorry_73_; uint8_t v_revert_74_; uint8_t v_funCC_75_; uint8_t v_reducible_76_; lean_object* v_maxSuggestions_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
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
v_anchorRefs_x3f_22_ = lean_ctor_get(v_ctx_11_, 5);
v_cheapCases_23_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*10);
v_reportMVarIssue_24_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*10 + 1);
v_splitSource_25_ = lean_ctor_get(v_ctx_11_, 6);
v_ematchDiagSource_26_ = lean_ctor_get(v_ctx_11_, 7);
v_symPrios_27_ = lean_ctor_get(v_ctx_11_, 8);
v_extensions_28_ = lean_ctor_get(v_ctx_11_, 9);
v_debug_29_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*10 + 2);
v_ematchDiag_30_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*10 + 3);
v_markInstances_31_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 1);
v_lax_32_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 2);
v_suggestions_33_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 3);
v_locals_34_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 4);
v_splits_35_ = lean_ctor_get(v_config_12_, 0);
v_ematch_36_ = lean_ctor_get(v_config_12_, 1);
v_gen_37_ = lean_ctor_get(v_config_12_, 2);
v_genLocal_38_ = lean_ctor_get(v_config_12_, 3);
v_instances_39_ = lean_ctor_get(v_config_12_, 4);
v_matchEqs_40_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 5);
v_splitMatch_41_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 6);
v_splitIte_42_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 7);
v_splitIndPred_43_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 8);
v_splitImp_44_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 9);
v_canonHeartbeats_45_ = lean_ctor_get(v_config_12_, 5);
v_ext_46_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 10);
v_extAll_47_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 11);
v_etaStruct_48_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 12);
v_funext_49_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 13);
v_lookahead_50_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 14);
v_verbose_51_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 15);
v_clean_52_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 16);
v_qlia_53_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 17);
v_mbtc_54_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 18);
v_zetaDelta_55_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 19);
v_zeta_56_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 20);
v_distrib_57_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 21);
v_ring_58_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 22);
v_ringSteps_59_ = lean_ctor_get(v_config_12_, 6);
v_ringMaxDegree_60_ = lean_ctor_get(v_config_12_, 7);
v_linarith_61_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 23);
v_lia_62_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 24);
v_liaSteps_63_ = lean_ctor_get(v_config_12_, 8);
v_hom_64_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 25);
v_ac_65_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 26);
v_acSteps_66_ = lean_ctor_get(v_config_12_, 9);
v_exp_67_ = lean_ctor_get(v_config_12_, 10);
v_abstractProof_68_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 27);
v_inj_69_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 28);
v_order_70_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 29);
v_min_71_ = lean_ctor_get(v_config_12_, 11);
v_detailed_72_ = lean_ctor_get(v_config_12_, 12);
v_useSorry_73_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 30);
v_revert_74_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 31);
v_funCC_75_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 32);
v_reducible_76_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 33);
v_maxSuggestions_77_ = lean_ctor_get(v_config_12_, 13);
v___x_78_ = 1;
lean_inc(v_maxSuggestions_77_);
lean_inc(v_detailed_72_);
lean_inc(v_min_71_);
lean_inc(v_exp_67_);
lean_inc(v_acSteps_66_);
lean_inc(v_liaSteps_63_);
lean_inc(v_ringMaxDegree_60_);
lean_inc(v_ringSteps_59_);
lean_inc(v_canonHeartbeats_45_);
lean_inc(v_instances_39_);
lean_inc(v_genLocal_38_);
lean_inc(v_gen_37_);
lean_inc(v_ematch_36_);
lean_inc(v_splits_35_);
v___x_79_ = lean_alloc_ctor(0, 14, 34);
lean_ctor_set(v___x_79_, 0, v_splits_35_);
lean_ctor_set(v___x_79_, 1, v_ematch_36_);
lean_ctor_set(v___x_79_, 2, v_gen_37_);
lean_ctor_set(v___x_79_, 3, v_genLocal_38_);
lean_ctor_set(v___x_79_, 4, v_instances_39_);
lean_ctor_set(v___x_79_, 5, v_canonHeartbeats_45_);
lean_ctor_set(v___x_79_, 6, v_ringSteps_59_);
lean_ctor_set(v___x_79_, 7, v_ringMaxDegree_60_);
lean_ctor_set(v___x_79_, 8, v_liaSteps_63_);
lean_ctor_set(v___x_79_, 9, v_acSteps_66_);
lean_ctor_set(v___x_79_, 10, v_exp_67_);
lean_ctor_set(v___x_79_, 11, v_min_71_);
lean_ctor_set(v___x_79_, 12, v_detailed_72_);
lean_ctor_set(v___x_79_, 13, v_maxSuggestions_77_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 1, v_markInstances_31_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 2, v_lax_32_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 3, v_suggestions_33_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 4, v_locals_34_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 5, v_matchEqs_40_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 6, v_splitMatch_41_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 7, v_splitIte_42_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 8, v_splitIndPred_43_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 9, v_splitImp_44_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 10, v_ext_46_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 11, v_extAll_47_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 12, v_etaStruct_48_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 13, v_funext_49_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 14, v_lookahead_50_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 15, v_verbose_51_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 16, v_clean_52_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 17, v_qlia_53_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 18, v_mbtc_54_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 19, v_zetaDelta_55_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 20, v_zeta_56_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 21, v_distrib_57_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 22, v_ring_58_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 23, v_linarith_61_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 24, v_lia_62_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 25, v_hom_64_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 26, v_ac_65_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 27, v_abstractProof_68_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 28, v_inj_69_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 29, v_order_70_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 30, v_useSorry_73_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 31, v_revert_74_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 32, v_funCC_75_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*14 + 33, v_reducible_76_);
lean_inc_ref(v_extensions_28_);
lean_inc_ref(v_symPrios_27_);
lean_inc(v_ematchDiagSource_26_);
lean_inc(v_splitSource_25_);
lean_inc(v_anchorRefs_x3f_22_);
lean_inc_ref(v_symDSimpMethods_21_);
lean_inc_ref(v_symSimpMethods_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_80_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_80_, 0, v_simp_18_);
lean_ctor_set(v___x_80_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_80_, 2, v_symSimpMethods_20_);
lean_ctor_set(v___x_80_, 3, v_symDSimpMethods_21_);
lean_ctor_set(v___x_80_, 4, v___x_79_);
lean_ctor_set(v___x_80_, 5, v_anchorRefs_x3f_22_);
lean_ctor_set(v___x_80_, 6, v_splitSource_25_);
lean_ctor_set(v___x_80_, 7, v_ematchDiagSource_26_);
lean_ctor_set(v___x_80_, 8, v_symPrios_27_);
lean_ctor_set(v___x_80_, 9, v_extensions_28_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*10, v_cheapCases_23_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*10 + 1, v_reportMVarIssue_24_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*10 + 2, v_debug_29_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*10 + 3, v_ematchDiag_30_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_81_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_81_, 0, v_toContext_13_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
lean_ctor_set(v___x_81_, 2, v_sctx_14_);
lean_ctor_set(v___x_81_, 3, v_methods_15_);
lean_ctor_set(v___x_81_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_82_ = lean_apply_9(v_x_1_, v___x_81_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_94_, lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_106_, lean_object* v_x_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_106_, v_x_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
return v_res_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_unbox(v_defValue_121_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v___x_123_, 1);
if (lean_obj_tag(v_val_125_) == 1)
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_val_125_, 0);
lean_dec_ref_known(v_val_125_, 0);
return v_v_126_;
}
else
{
uint8_t v___x_127_; 
lean_dec(v_val_125_);
v___x_127_ = lean_unbox(v_defValue_121_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Array_mkArray0___redArg();
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object* v_goal_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_seq_170_; lean_object* v_goal_171_; lean_object* v_seq_174_; lean_object* v___y_176_; uint8_t v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v_mvarId_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v_seq_239_; lean_object* v_goal_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_seq_174_ = lean_box(0);
v___x_284_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_166_);
v___x_285_ = l_Lean_Meta_tactic_hygienic;
v___x_286_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_284_, v___x_285_);
lean_dec_ref(v___x_284_);
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7));
lean_inc_ref(v_goal_158_);
v___x_288_ = l_Lean_Meta_Grind_Goal_intros(v_goal_158_, v___x_287_, v___x_286_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
if (lean_obj_tag(v_a_289_) == 1)
{
lean_object* v_goal_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_goal_158_);
v_goal_290_ = lean_ctor_get(v_a_289_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_a_289_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v_a_289_, 0);
lean_dec(v_unused_319_);
v___x_292_ = v_a_289_;
v_isShared_293_ = v_isSharedCheck_318_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_goal_290_);
lean_dec(v_a_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_318_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_290_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v_ref_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v_ref_296_ = lean_ctor_get(v_a_166_, 2);
v___x_297_ = 0;
v___x_298_ = l_Lean_SourceInfo_fromRef(v_ref_296_, v___x_297_);
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9));
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10));
lean_inc(v___x_298_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 2);
lean_ctor_set(v___x_292_, 1, v___x_300_);
lean_ctor_set(v___x_292_, 0, v___x_298_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_309_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12));
v___x_304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13);
lean_inc(v___x_298_);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_298_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_304_);
v___x_306_ = l_Lean_Syntax_node2(v___x_298_, v___x_299_, v___x_302_, v___x_305_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_seq_174_);
v___x_308_ = l_List_appendTR___redArg(v_seq_174_, v___x_307_);
v_seq_239_ = v___x_308_;
v_goal_240_ = v_a_295_;
v___y_241_ = v_a_159_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
goto v___jp_238_;
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_del_object(v___x_292_);
v_a_310_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_294_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_294_);
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
else
{
lean_dec(v_a_289_);
v_seq_239_ = v_seq_174_;
v_goal_240_ = v_goal_158_;
v___y_241_ = v_a_159_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
goto v___jp_238_;
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_goal_158_);
v_a_320_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_288_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_288_);
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
v___jp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_seq_170_);
lean_ctor_set(v___x_172_, 1, v_goal_171_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
v___jp_175_:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_MVarId_byContra_x3f(v_mvarId_180_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
if (lean_obj_tag(v_a_191_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_193_; 
lean_dec_ref(v___y_179_);
v_val_192_ = lean_ctor_get(v_a_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_a_191_, 1);
v___x_193_ = l_Lean_Meta_intro1Core(v_val_192_, v___y_177_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_snd_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_220_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_snd_195_ = lean_ctor_get(v_a_194_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v_a_194_, 0);
lean_dec(v_unused_221_);
v___x_197_ = v_a_194_;
v_isShared_198_ = v_isSharedCheck_220_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_snd_195_);
lean_dec(v_a_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_220_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___y_178_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___y_178_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_snd_195_);
v___x_200_ = v_reuseFailAlloc_219_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Grind_Goal_internalizeAll(v___x_200_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_ref_203_ = lean_ctor_get(v___y_188_, 2);
v___x_204_ = l_Lean_SourceInfo_fromRef(v_ref_203_, v___y_177_);
v___x_205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5));
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6));
lean_inc(v___x_204_);
v___x_207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_204_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = l_Lean_Syntax_node1(v___x_204_, v___x_205_, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v_seq_174_);
v___x_210_ = l_List_appendTR___redArg(v___y_176_, v___x_209_);
v_seq_170_ = v___x_210_;
v_goal_171_ = v_a_202_;
goto v___jp_169_;
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v___y_176_);
v_a_211_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_201_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_201_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___y_178_);
lean_dec(v___y_176_);
v_a_222_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_193_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_193_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_dec(v_a_191_);
lean_dec_ref(v___y_178_);
v_seq_170_ = v___y_176_;
v_goal_171_ = v___y_179_;
goto v___jp_169_;
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_176_);
v_a_230_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_190_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_190_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
v___jp_238_:
{
lean_object* v_toGoalState_250_; lean_object* v_mvarId_251_; lean_object* v___x_252_; 
v_toGoalState_250_ = lean_ctor_get(v_goal_240_, 0);
v_mvarId_251_ = lean_ctor_get(v_goal_240_, 1);
lean_inc(v_mvarId_251_);
v___x_252_ = l_Lean_MVarId_getType(v_mvarId_251_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; uint8_t v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_n(v_a_253_, 2);
lean_dec_ref_known(v___x_252_, 1);
v___x_254_ = l_Lean_Expr_isFalse(v_a_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_inc_ref(v_toGoalState_250_);
v___x_255_ = l_Lean_Meta_isProp(v_a_253_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = lean_unbox(v_a_256_);
lean_dec(v_a_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_inc(v_mvarId_251_);
v___x_258_ = l_Lean_MVarId_exfalso(v_mvarId_251_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v___y_176_ = v_seq_239_;
v___y_177_ = v___x_254_;
v___y_178_ = v_toGoalState_250_;
v___y_179_ = v_goal_240_;
v_mvarId_180_ = v_a_259_;
v___y_181_ = v___y_241_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
goto v___jp_175_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_toGoalState_250_);
lean_dec_ref(v_goal_240_);
lean_dec(v_seq_239_);
v_a_260_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_258_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_inc(v_mvarId_251_);
v___y_176_ = v_seq_239_;
v___y_177_ = v___x_254_;
v___y_178_ = v_toGoalState_250_;
v___y_179_ = v_goal_240_;
v_mvarId_180_ = v_mvarId_251_;
v___y_181_ = v___y_241_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
goto v___jp_175_;
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v_toGoalState_250_);
lean_dec_ref(v_goal_240_);
lean_dec(v_seq_239_);
v_a_268_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_255_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_255_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_dec(v_a_253_);
v_seq_170_ = v_seq_239_;
v_goal_171_ = v_goal_240_;
goto v___jp_169_;
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_goal_240_);
lean_dec(v_seq_239_);
v_a_276_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_252_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_252_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object* v_goal_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_goal_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_box(0);
v___x_341_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; uint8_t v___x_378_; lean_object* v_env_379_; lean_object* v___x_380_; lean_object* v_toCold_381_; lean_object* v_mctx_382_; lean_object* v_lctx_383_; lean_object* v_options_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = 0;
v_env_379_ = l_Lean_Environment_setRecordingDeps(v_env_377_, v___x_378_);
v___x_380_ = lean_st_ref_get(v___y_372_);
v_toCold_381_ = lean_ctor_get(v___y_373_, 0);
v_mctx_382_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_mctx_382_);
lean_dec(v___x_380_);
v_lctx_383_ = lean_ctor_get(v___y_371_, 2);
v_options_384_ = lean_ctor_get(v_toCold_381_, 2);
lean_inc_ref(v_options_384_);
lean_inc_ref(v_lctx_383_);
v___x_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_385_, 0, v_env_379_);
lean_ctor_set(v___x_385_, 1, v_mctx_382_);
lean_ctor_set(v___x_385_, 2, v_lctx_383_);
lean_ctor_set(v___x_385_, 3, v_options_384_);
v___x_386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_msgData_370_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object* v_msgData_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msgData_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_ref_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_ref_401_ = lean_ctor_get(v___y_398_, 2);
v___x_402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
lean_inc(v_ref_401_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_ref_401_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 1)
{
lean_object* v_pre_428_; 
v_pre_428_ = lean_ctor_get(v_x_427_, 0);
switch(lean_obj_tag(v_pre_428_))
{
case 1:
{
lean_object* v_pre_429_; 
v_pre_429_ = lean_ctor_get(v_pre_428_, 0);
switch(lean_obj_tag(v_pre_429_))
{
case 0:
{
lean_object* v_str_430_; lean_object* v_str_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_str_430_ = lean_ctor_get(v_x_427_, 1);
v_str_431_ = lean_ctor_get(v_pre_428_, 1);
v___x_432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_433_ = lean_string_dec_eq(v_str_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_435_ = lean_string_dec_eq(v_str_431_, v___x_434_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_437_ = lean_string_dec_eq(v_str_430_, v___x_436_);
if (v___x_437_ == 0)
{
return v___x_437_;
}
else
{
return v_suppressElabErrors_426_;
}
}
}
else
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_439_ = lean_string_dec_eq(v_str_430_, v___x_438_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
return v_suppressElabErrors_426_;
}
}
}
case 1:
{
lean_object* v_pre_440_; 
v_pre_440_ = lean_ctor_get(v_pre_429_, 0);
if (lean_obj_tag(v_pre_440_) == 0)
{
lean_object* v_str_441_; lean_object* v_str_442_; lean_object* v_str_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_str_441_ = lean_ctor_get(v_x_427_, 1);
v_str_442_ = lean_ctor_get(v_pre_428_, 1);
v_str_443_ = lean_ctor_get(v_pre_429_, 1);
v___x_444_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_445_ = lean_string_dec_eq(v_str_443_, v___x_444_);
if (v___x_445_ == 0)
{
return v___x_445_;
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_447_ = lean_string_dec_eq(v_str_442_, v___x_446_);
if (v___x_447_ == 0)
{
return v___x_447_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_449_ = lean_string_dec_eq(v_str_441_, v___x_448_);
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
return v_suppressElabErrors_426_;
}
}
}
}
else
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
}
default: 
{
uint8_t v___x_451_; 
v___x_451_ = 0;
return v___x_451_;
}
}
}
case 0:
{
lean_object* v_str_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_str_452_ = lean_ctor_get(v_x_427_, 1);
v___x_453_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_454_ = lean_string_dec_eq(v_str_452_, v___x_453_);
if (v___x_454_ == 0)
{
return v___x_454_;
}
else
{
return v_suppressElabErrors_426_;
}
}
default: 
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_457_, lean_object* v_x_458_){
_start:
{
uint8_t v_suppressElabErrors_boxed_459_; uint8_t v_res_460_; lean_object* v_r_461_; 
v_suppressElabErrors_boxed_459_ = lean_unbox(v_suppressElabErrors_457_);
v_res_460_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_459_, v_x_458_);
lean_dec(v_x_458_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_463_, lean_object* v_msgData_464_, uint8_t v_severity_465_, uint8_t v_isSilent_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___y_473_; lean_object* v___y_474_; uint8_t v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v_toCold_480_; lean_object* v___y_481_; lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; uint8_t v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; uint8_t v___y_547_; uint8_t v___y_548_; uint8_t v___x_558_; uint8_t v___y_560_; uint8_t v___x_566_; 
v___x_558_ = 2;
v___x_566_ = l_Lean_instBEqMessageSeverity_beq(v_severity_465_, v___x_558_);
if (v___x_566_ == 0)
{
v___y_560_ = v___x_566_;
goto v___jp_559_;
}
else
{
uint8_t v___x_567_; 
lean_inc_ref(v_msgData_464_);
v___x_567_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_464_);
if (v___x_567_ == 0)
{
v___y_560_ = v___x_567_;
goto v___jp_559_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_msgData_464_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
v___jp_472_:
{
lean_object* v_currNamespace_482_; lean_object* v_openDecls_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_nextMacroScope_489_; lean_object* v_ngen_490_; lean_object* v_auxDeclNGen_491_; lean_object* v_traceState_492_; lean_object* v_cache_493_; lean_object* v_recordedDeps_494_; lean_object* v_messages_495_; lean_object* v_infoState_496_; lean_object* v_snapshotTasks_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v_currNamespace_482_ = lean_ctor_get(v_toCold_480_, 4);
v_openDecls_483_ = lean_ctor_get(v_toCold_480_, 5);
lean_inc(v_openDecls_483_);
lean_inc(v_currNamespace_482_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_currNamespace_482_);
lean_ctor_set(v___x_484_, 1, v_openDecls_483_);
v___x_485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___y_479_);
lean_inc_ref(v___y_478_);
lean_inc_ref(v___y_477_);
v___x_486_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_486_, 0, v___y_477_);
lean_ctor_set(v___x_486_, 1, v___y_474_);
lean_ctor_set(v___x_486_, 2, v___y_476_);
lean_ctor_set(v___x_486_, 3, v___y_478_);
lean_ctor_set(v___x_486_, 4, v___x_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5, v___y_473_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 1, v___y_475_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*5 + 2, v_isSilent_466_);
v___x_487_ = lean_st_ref_take(v___y_481_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
v_nextMacroScope_489_ = lean_ctor_get(v___x_487_, 1);
v_ngen_490_ = lean_ctor_get(v___x_487_, 2);
v_auxDeclNGen_491_ = lean_ctor_get(v___x_487_, 3);
v_traceState_492_ = lean_ctor_get(v___x_487_, 4);
v_cache_493_ = lean_ctor_get(v___x_487_, 5);
v_recordedDeps_494_ = lean_ctor_get(v___x_487_, 6);
v_messages_495_ = lean_ctor_get(v___x_487_, 7);
v_infoState_496_ = lean_ctor_get(v___x_487_, 8);
v_snapshotTasks_497_ = lean_ctor_get(v___x_487_, 9);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_508_ == 0)
{
v___x_499_ = v___x_487_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snapshotTasks_497_);
lean_inc(v_infoState_496_);
lean_inc(v_messages_495_);
lean_inc(v_recordedDeps_494_);
lean_inc(v_cache_493_);
lean_inc(v_traceState_492_);
lean_inc(v_auxDeclNGen_491_);
lean_inc(v_ngen_490_);
lean_inc(v_nextMacroScope_489_);
lean_inc(v_env_488_);
lean_dec(v___x_487_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_MessageLog_add(v___x_486_, v_messages_495_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 7, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_env_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_nextMacroScope_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_ngen_490_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_auxDeclNGen_491_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_traceState_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_cache_493_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_recordedDeps_494_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_infoState_496_);
lean_ctor_set(v_reuseFailAlloc_507_, 9, v_snapshotTasks_497_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_st_ref_put(v___y_481_, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_501_);
return v___x_506_;
}
}
}
v___jp_509_:
{
lean_object* v_fileName_518_; lean_object* v_fileMap_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_535_; 
v_fileName_518_ = lean_ctor_get(v___y_515_, 0);
v_fileMap_519_ = lean_ctor_get(v___y_515_, 1);
v___x_520_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_464_);
v___x_521_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v___x_520_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_535_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc_ref_n(v_fileMap_519_, 2);
v___x_526_ = l_Lean_FileMap_toPosition(v_fileMap_519_, v___y_513_);
lean_dec(v___y_513_);
v___x_527_ = l_Lean_FileMap_toPosition(v_fileMap_519_, v___y_517_);
lean_dec(v___y_517_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0));
if (v___y_516_ == 0)
{
lean_del_object(v___x_524_);
lean_dec_ref(v___y_511_);
v___y_473_ = v___y_512_;
v___y_474_ = v___x_526_;
v___y_475_ = v___y_514_;
v___y_476_ = v___x_528_;
v___y_477_ = v_fileName_518_;
v___y_478_ = v___x_529_;
v___y_479_ = v_a_522_;
v_toCold_480_ = v___y_510_;
v___y_481_ = v___y_470_;
goto v___jp_472_;
}
else
{
uint8_t v___x_530_; 
lean_inc(v_a_522_);
v___x_530_ = l_Lean_MessageData_hasTag(v___y_511_, v_a_522_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_533_; 
lean_dec_ref_known(v___x_528_, 1);
lean_dec_ref(v___x_526_);
lean_dec(v_a_522_);
v___x_531_ = lean_box(0);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_531_);
v___x_533_ = v___x_524_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_del_object(v___x_524_);
v___y_473_ = v___y_512_;
v___y_474_ = v___x_526_;
v___y_475_ = v___y_514_;
v___y_476_ = v___x_528_;
v___y_477_ = v_fileName_518_;
v___y_478_ = v___x_529_;
v___y_479_ = v_a_522_;
v_toCold_480_ = v___y_510_;
v___y_481_ = v___y_470_;
goto v___jp_472_;
}
}
}
}
v___jp_536_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_540_);
lean_dec(v___y_542_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_inc(v___y_543_);
v___y_510_ = v___y_537_;
v___y_511_ = v___y_538_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_543_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_537_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_543_;
goto v___jp_509_;
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_544_, 1);
v___y_510_ = v___y_537_;
v___y_511_ = v___y_538_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_543_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_537_;
v___y_516_ = v___y_539_;
v___y_517_ = v_val_545_;
goto v___jp_509_;
}
}
v___jp_546_:
{
lean_object* v_toCold_549_; lean_object* v_ref_550_; uint8_t v_suppressElabErrors_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v_ref_554_; lean_object* v___x_555_; 
v_toCold_549_ = lean_ctor_get(v___y_469_, 0);
v_ref_550_ = lean_ctor_get(v___y_469_, 2);
v_suppressElabErrors_551_ = lean_ctor_get_uint8(v___y_469_, sizeof(void*)*3 + 2);
v___x_552_ = lean_box(v_suppressElabErrors_551_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_553_, 0, v___x_552_);
v_ref_554_ = l_Lean_replaceRef(v_ref_463_, v_ref_550_);
v___x_555_ = l_Lean_Syntax_getPos_x3f(v_ref_554_, v___y_547_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___y_537_ = v_toCold_549_;
v___y_538_ = v___f_553_;
v___y_539_ = v_suppressElabErrors_551_;
v___y_540_ = v___y_547_;
v___y_541_ = v___y_548_;
v___y_542_ = v_ref_554_;
v___y_543_ = v___x_556_;
goto v___jp_536_;
}
else
{
lean_object* v_val_557_; 
v_val_557_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v___x_555_, 1);
v___y_537_ = v_toCold_549_;
v___y_538_ = v___f_553_;
v___y_539_ = v_suppressElabErrors_551_;
v___y_540_ = v___y_547_;
v___y_541_ = v___y_548_;
v___y_542_ = v_ref_554_;
v___y_543_ = v_val_557_;
goto v___jp_536_;
}
}
v___jp_559_:
{
uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 1;
v___x_562_ = l_Lean_instBEqMessageSeverity_beq(v_severity_465_, v___x_561_);
if (v___x_562_ == 0)
{
v___y_547_ = v___y_560_;
v___y_548_ = v_severity_465_;
goto v___jp_546_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_469_);
v___x_564_ = l_Lean_warningAsError;
v___x_565_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_563_, v___x_564_);
lean_dec_ref(v___x_563_);
if (v___x_565_ == 0)
{
v___y_547_ = v___y_560_;
v___y_548_ = v_severity_465_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___y_560_;
v___y_548_ = v___x_558_;
goto v___jp_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_570_, lean_object* v_msgData_571_, lean_object* v_severity_572_, lean_object* v_isSilent_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_severity_boxed_579_; uint8_t v_isSilent_boxed_580_; lean_object* v_res_581_; 
v_severity_boxed_579_ = lean_unbox(v_severity_572_);
v_isSilent_boxed_580_ = lean_unbox(v_isSilent_573_);
v_res_581_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_570_, v_msgData_571_, v_severity_boxed_579_, v_isSilent_boxed_580_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v_ref_570_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_582_, uint8_t v_severity_583_, uint8_t v_isSilent_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_ref_595_; lean_object* v___x_596_; 
v_ref_595_ = lean_ctor_get(v___y_592_, 2);
v___x_596_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_595_, v_msgData_582_, v_severity_583_, v_isSilent_584_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_597_, lean_object* v_severity_598_, lean_object* v_isSilent_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v_severity_boxed_610_; uint8_t v_isSilent_boxed_611_; lean_object* v_res_612_; 
v_severity_boxed_610_ = lean_unbox(v_severity_598_);
v_isSilent_boxed_611_ = lean_unbox(v_isSilent_599_);
v_res_612_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_597_, v_severity_boxed_610_, v_isSilent_boxed_611_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_msgData_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = 1;
v___x_625_ = 0;
v___x_626_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_613_, v___x_624_, v___x_625_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_msgData_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_msgData_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v___x_657_, lean_object* v_stx_658_, uint8_t v___x_659_, lean_object* v___x_660_, lean_object* v___x_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v_a_669_, lean_object* v_params_670_, lean_object* v_____x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_suggestions_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_905_; 
v_fst_733_ = lean_ctor_get(v_____x_671_, 0);
v_snd_734_ = lean_ctor_get(v_____x_671_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_____x_671_);
if (v_isSharedCheck_905_ == 0)
{
v___x_736_ = v_____x_671_;
v_isShared_737_ = v_isSharedCheck_905_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v_____x_671_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_905_;
goto v_resetjp_735_;
}
v___jp_682_:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v_suggestions_683_);
v___x_687_ = lean_nat_dec_eq(v___x_686_, v___x_657_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_688_ = lean_box(0);
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_690_ = 4;
v___x_691_ = l_Lean_MessageData_nil;
v___x_692_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_658_, v_suggestions_683_, v___x_688_, v___x_689_, v___x_688_, v___x_690_, v___x_691_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v___x_692_, 0);
lean_dec(v_unused_701_);
v___x_694_ = v___x_692_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_dec(v___x_692_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_box(v___x_659_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_710_ = lean_array_get(v___x_660_, v_suggestions_683_, v___x_661_);
lean_dec_ref(v_suggestions_683_);
v___x_711_ = lean_box(0);
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_713_ = 4;
v___x_714_ = l_Lean_MessageData_nil;
v___x_715_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_658_, v___x_710_, v___x_711_, v___x_712_, v___x_711_, v___x_713_, v___x_714_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_715_, 0);
lean_dec(v_unused_724_);
v___x_717_ = v___x_715_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_dec(v___x_715_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_box(v___x_659_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_715_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_715_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
v_resetjp_735_:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Grind_Action_run(v_snd_734_, v_a_662_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
if (lean_obj_tag(v_a_739_) == 0)
{
lean_object* v_seq_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_847_; 
v_seq_740_ = lean_ctor_get(v_a_739_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_847_ == 0)
{
v___x_742_ = v_a_739_;
v_isShared_743_ = v_isSharedCheck_847_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_seq_740_);
lean_dec(v_a_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_847_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = l_List_appendTR___redArg(v_fst_733_, v_seq_740_);
lean_inc(v___x_744_);
v___x_745_ = l_Lean_Meta_Grind_mkFinishTactic(v___x_744_, v_a_663_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v_suggestions_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_suggestions_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___x_830_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
lean_inc_n(v___x_744_, 2);
v___x_747_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v___x_744_);
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_661_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_669_);
lean_inc_ref(v_a_664_);
lean_inc_ref(v___x_808_);
v___x_830_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_808_, v_a_664_, v___x_744_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; uint8_t v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
if (v___x_832_ == 0)
{
v_suggestions_810_ = v___x_807_;
v___y_811_ = v___y_672_;
v___y_812_ = v___y_673_;
v___y_813_ = v___y_674_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
goto v___jp_809_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
lean_inc_ref(v___x_668_);
lean_inc_ref(v___x_667_);
lean_inc_ref(v___x_666_);
lean_inc_ref(v___x_665_);
v___x_834_ = l_Lean_Name_mkStr5(v___x_665_, v___x_666_, v___x_667_, v___x_668_, v___x_833_);
lean_inc(v___x_747_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_747_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
lean_ctor_set(v___x_837_, 3, v___x_836_);
lean_ctor_set(v___x_837_, 4, v___x_836_);
lean_ctor_set(v___x_837_, 5, v___x_836_);
v___x_838_ = lean_array_push(v___x_807_, v___x_837_);
v_suggestions_810_ = v___x_838_;
v___y_811_ = v___y_672_;
v___y_812_ = v___y_673_;
v___y_813_ = v___y_674_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
goto v___jp_809_;
}
}
else
{
lean_dec_ref_known(v___x_808_, 1);
lean_dec_ref(v___x_807_);
lean_dec(v___x_747_);
lean_dec(v_a_746_);
lean_dec(v___x_744_);
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
return v___x_830_;
}
v___jp_748_:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_suggestions_749_);
v___x_760_ = lean_nat_dec_eq(v___x_759_, v___x_661_);
if (v___x_760_ == 0)
{
lean_dec(v___x_747_);
lean_dec(v___x_744_);
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
v_suggestions_683_ = v_suggestions_749_;
v___y_684_ = v___y_757_;
v___y_685_ = v___y_758_;
goto v___jp_682_;
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v_suggestions_749_);
v___x_761_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v___x_744_, v___y_757_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v_mvarId_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_797_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v_mvarId_763_ = lean_ctor_get(v_a_664_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_a_664_, 0);
lean_dec(v_unused_798_);
v___x_765_ = v_a_664_;
v_isShared_766_ = v_isSharedCheck_797_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_mvarId_763_);
lean_dec(v_a_664_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_797_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3);
v___x_768_ = l_Lean_MessageData_ofSyntax(v_a_762_);
v___x_769_ = l_Lean_indentD(v___x_768_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 7);
lean_ctor_set(v___x_765_, 1, v___x_769_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_796_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 7);
lean_ctor_set(v___x_736_, 1, v___x_772_);
lean_ctor_set(v___x_736_, 0, v___x_771_);
v___x_774_ = v___x_736_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_795_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v_mvarId_763_);
v___x_776_ = v___x_742_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_mvarId_763_);
v___x_776_ = v_reuseFailAlloc_794_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v___x_777_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref_known(v___x_778_, 1);
v___x_779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
v___x_780_ = l_Lean_Name_mkStr5(v___x_665_, v___x_666_, v___x_667_, v___x_668_, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_747_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
lean_ctor_set(v___x_783_, 3, v___x_782_);
lean_ctor_set(v___x_783_, 4, v___x_782_);
lean_ctor_set(v___x_783_, 5, v___x_782_);
v___x_784_ = lean_mk_empty_array_with_capacity(v___x_657_);
v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
v_suggestions_683_ = v___x_785_;
v___y_684_ = v___y_757_;
v___y_685_ = v___y_758_;
goto v___jp_682_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___x_747_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec(v_stx_658_);
v_a_786_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_778_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_778_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
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
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v___x_747_);
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
v_a_799_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_761_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_761_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
v___jp_809_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
lean_inc(v_a_746_);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_746_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
lean_inc_ref(v_a_664_);
v___x_822_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_808_, v_a_664_, v___x_821_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; uint8_t v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_unbox(v_a_823_);
lean_dec(v_a_823_);
if (v___x_824_ == 0)
{
lean_dec(v_a_746_);
v_suggestions_749_ = v_suggestions_810_;
v___y_750_ = v___y_811_;
v___y_751_ = v___y_812_;
v___y_752_ = v___y_813_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
goto v___jp_748_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8));
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_a_746_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
lean_ctor_set(v___x_828_, 4, v___x_827_);
lean_ctor_set(v___x_828_, 5, v___x_827_);
v___x_829_ = lean_array_push(v_suggestions_810_, v___x_828_);
v_suggestions_749_ = v___x_829_;
v___y_750_ = v___y_811_;
v___y_751_ = v___y_812_;
v___y_752_ = v___y_813_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
goto v___jp_748_;
}
}
else
{
lean_dec_ref(v_suggestions_810_);
lean_dec(v___x_747_);
lean_dec(v_a_746_);
lean_dec(v___x_744_);
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
return v___x_822_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v___x_744_);
lean_del_object(v___x_742_);
lean_del_object(v___x_736_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
v_a_839_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_745_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_745_);
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
}
}
else
{
lean_object* v_gs_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_736_);
lean_dec(v_fst_733_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
v_gs_848_ = lean_ctor_get(v_a_739_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_896_ == 0)
{
v___x_850_ = v_a_739_;
v_isShared_851_ = v_isSharedCheck_896_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_gs_848_);
lean_dec(v_a_739_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_896_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
if (lean_obj_tag(v_gs_848_) == 1)
{
lean_object* v_head_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_892_; 
v_head_852_ = lean_ctor_get(v_gs_848_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_gs_848_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_gs_848_, 1);
lean_dec(v_unused_893_);
v___x_854_ = v_gs_848_;
v_isShared_855_ = v_isSharedCheck_892_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_head_852_);
lean_dec(v_gs_848_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_892_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_head_852_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_head_852_);
v___x_857_ = v_reuseFailAlloc_891_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_Grind_mkResult(v_params_670_, v___x_857_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_859_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 7);
lean_ctor_set(v___x_854_, 1, v_a_861_);
lean_ctor_set(v___x_854_, 0, v___x_862_);
v___x_864_ = v___x_854_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_861_);
v___x_864_ = v_reuseFailAlloc_874_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v___x_865_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_864_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_854_);
v_a_875_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_860_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_860_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_del_object(v___x_854_);
v_a_883_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_858_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_858_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_850_);
lean_dec(v_gs_848_);
v___x_894_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12);
v___x_895_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_894_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_736_);
lean_dec(v_fst_733_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_stx_658_);
v_a_897_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_738_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_738_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v___x_906_ = _args[0];
lean_object* v_stx_907_ = _args[1];
lean_object* v___x_908_ = _args[2];
lean_object* v___x_909_ = _args[3];
lean_object* v___x_910_ = _args[4];
lean_object* v_a_911_ = _args[5];
lean_object* v_a_912_ = _args[6];
lean_object* v_a_913_ = _args[7];
lean_object* v___x_914_ = _args[8];
lean_object* v___x_915_ = _args[9];
lean_object* v___x_916_ = _args[10];
lean_object* v___x_917_ = _args[11];
lean_object* v_a_918_ = _args[12];
lean_object* v_params_919_ = _args[13];
lean_object* v_____x_920_ = _args[14];
lean_object* v___y_921_ = _args[15];
lean_object* v___y_922_ = _args[16];
lean_object* v___y_923_ = _args[17];
lean_object* v___y_924_ = _args[18];
lean_object* v___y_925_ = _args[19];
lean_object* v___y_926_ = _args[20];
lean_object* v___y_927_ = _args[21];
lean_object* v___y_928_ = _args[22];
lean_object* v___y_929_ = _args[23];
lean_object* v___y_930_ = _args[24];
_start:
{
uint8_t v___x_49627__boxed_931_; lean_object* v_res_932_; 
v___x_49627__boxed_931_ = lean_unbox(v___x_908_);
v_res_932_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v___x_906_, v_stx_907_, v___x_49627__boxed_931_, v___x_909_, v___x_910_, v_a_911_, v_a_912_, v_a_913_, v___x_914_, v___x_915_, v___x_916_, v___x_917_, v_a_918_, v_params_919_, v_____x_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v_params_919_);
lean_dec_ref(v_a_912_);
lean_dec(v___x_910_);
lean_dec_ref(v___x_909_);
lean_dec(v___x_906_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t v_sym_933_, lean_object* v_a_934_, lean_object* v___f_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
if (v_sym_933_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_934_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
v___x_948_ = lean_apply_11(v___f_935_, v___x_947_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_948_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_a_934_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
v___x_951_ = lean_apply_11(v___f_935_, v_a_950_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_951_;
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v___f_935_);
v_a_952_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_949_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v_sym_960_, lean_object* v_a_961_, lean_object* v___f_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_sym_boxed_973_; lean_object* v_res_974_; 
v_sym_boxed_973_ = lean_unbox(v_sym_960_);
v_res_974_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v_sym_boxed_973_, v_a_961_, v___f_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___y_975_, v___y_976_, v___y_977_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_997_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_unbox(v_a_986_);
lean_dec(v_a_986_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_988_);
v___x_995_ = lean_box(0);
v___x_996_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_995_, v___y_977_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
return v___x_996_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_985_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_985_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_stx_1019_, uint8_t v___x_1020_, lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_ref_1039_; lean_object* v___x_1040_; 
v_ref_1039_ = lean_ctor_get(v___y_1036_, 2);
v___x_1040_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1017_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1031_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_params_1044_; uint8_t v_sym_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___y_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_params_1044_ = lean_ctor_get(v___y_1030_, 4);
v_sym_1045_ = lean_ctor_get_uint8(v___y_1030_, sizeof(void*)*5);
v___x_1046_ = lean_box(v___x_1020_);
lean_inc_ref(v_params_1044_);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 25, 14);
lean_closure_set(v___f_1047_, 0, v___x_1018_);
lean_closure_set(v___f_1047_, 1, v_stx_1019_);
lean_closure_set(v___f_1047_, 2, v___x_1046_);
lean_closure_set(v___f_1047_, 3, v___x_1021_);
lean_closure_set(v___f_1047_, 4, v___x_1022_);
lean_closure_set(v___f_1047_, 5, v_a_1041_);
lean_closure_set(v___f_1047_, 6, v_a_1023_);
lean_closure_set(v___f_1047_, 7, v_a_1024_);
lean_closure_set(v___f_1047_, 8, v___x_1025_);
lean_closure_set(v___f_1047_, 9, v___x_1026_);
lean_closure_set(v___f_1047_, 10, v___x_1027_);
lean_closure_set(v___f_1047_, 11, v___x_1028_);
lean_closure_set(v___f_1047_, 12, v_a_1029_);
lean_closure_set(v___f_1047_, 13, v_params_1044_);
v___x_1048_ = lean_box(v_sym_1045_);
v___y_1049_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 13, 3);
lean_closure_set(v___y_1049_, 0, v___x_1048_);
lean_closure_set(v___y_1049_, 1, v_a_1043_);
lean_closure_set(v___y_1049_, 2, v___f_1047_);
v___f_1050_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1050_, 0, v___y_1049_);
v___x_1051_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1050_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec_ref(v___y_1030_);
return v___x_1051_;
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_a_1041_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_a_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v___x_1022_);
lean_dec_ref(v___x_1021_);
lean_dec(v_stx_1019_);
lean_dec(v___x_1018_);
v_a_1052_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1042_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1042_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_a_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v___x_1022_);
lean_dec_ref(v___x_1021_);
lean_dec(v_stx_1019_);
lean_dec(v___x_1018_);
v_a_1060_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1062_ = v___x_1040_;
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1040_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1064_ = lean_io_error_to_string(v_a_1060_);
v___x_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
lean_inc(v_ref_1039_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_ref_1039_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1067_);
v___x_1069_ = v___x_1062_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___x_1072_ = _args[0];
lean_object* v___x_1073_ = _args[1];
lean_object* v_stx_1074_ = _args[2];
lean_object* v___x_1075_ = _args[3];
lean_object* v___x_1076_ = _args[4];
lean_object* v___x_1077_ = _args[5];
lean_object* v_a_1078_ = _args[6];
lean_object* v_a_1079_ = _args[7];
lean_object* v___x_1080_ = _args[8];
lean_object* v___x_1081_ = _args[9];
lean_object* v___x_1082_ = _args[10];
lean_object* v___x_1083_ = _args[11];
lean_object* v_a_1084_ = _args[12];
lean_object* v___y_1085_ = _args[13];
lean_object* v___y_1086_ = _args[14];
lean_object* v___y_1087_ = _args[15];
lean_object* v___y_1088_ = _args[16];
lean_object* v___y_1089_ = _args[17];
lean_object* v___y_1090_ = _args[18];
lean_object* v___y_1091_ = _args[19];
lean_object* v___y_1092_ = _args[20];
lean_object* v___y_1093_ = _args[21];
_start:
{
uint8_t v___x_50298__boxed_1094_; lean_object* v_res_1095_; 
v___x_50298__boxed_1094_ = lean_unbox(v___x_1075_);
v_res_1095_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___x_1072_, v___x_1073_, v_stx_1074_, v___x_50298__boxed_1094_, v___x_1076_, v___x_1077_, v_a_1078_, v_a_1079_, v___x_1080_, v___x_1081_, v___x_1082_, v___x_1083_, v_a_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v_stx_1099_, uint8_t v___x_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_only_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v___x_1097_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1109_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0));
v___x_1122_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1121_, v___y_1108_, v___y_1109_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v_params_1124_; uint8_t v___y_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v_params_1124_ = lean_ctor_get(v___y_1108_, 4);
lean_inc_ref(v_params_1124_);
if (lean_obj_tag(v_only_1107_) == 0)
{
uint8_t v___x_1131_; 
v___x_1131_ = 0;
v___y_1126_ = v___x_1131_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___x_1100_;
goto v___jp_1125_;
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_unsigned_to_nat(10000u);
v___x_1128_ = lean_box(v___x_1100_);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 22, 13);
lean_closure_set(v___f_1129_, 0, v___x_1127_);
lean_closure_set(v___f_1129_, 1, v___x_1098_);
lean_closure_set(v___f_1129_, 2, v_stx_1099_);
lean_closure_set(v___f_1129_, 3, v___x_1128_);
lean_closure_set(v___f_1129_, 4, v___x_1101_);
lean_closure_set(v___f_1129_, 5, v___x_1102_);
lean_closure_set(v___f_1129_, 6, v_a_1118_);
lean_closure_set(v___f_1129_, 7, v_a_1120_);
lean_closure_set(v___f_1129_, 8, v___x_1103_);
lean_closure_set(v___f_1129_, 9, v___x_1104_);
lean_closure_set(v___f_1129_, 10, v___x_1105_);
lean_closure_set(v___f_1129_, 11, v___x_1106_);
lean_closure_set(v___f_1129_, 12, v_a_1123_);
v___x_1130_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_1124_, v___x_1097_, v___y_1126_, v___f_1129_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec_ref(v___y_1108_);
return v___x_1130_;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_a_1120_);
lean_dec(v_a_1118_);
lean_dec_ref(v___y_1108_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
lean_dec(v_stx_1099_);
lean_dec(v___x_1098_);
v_a_1132_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1122_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1118_);
lean_dec_ref(v___y_1108_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
lean_dec(v_stx_1099_);
lean_dec(v___x_1098_);
v_a_1140_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1119_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1119_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v___y_1108_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v___x_1101_);
lean_dec(v_stx_1099_);
lean_dec(v___x_1098_);
v_a_1148_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1117_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1117_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object** _args){
lean_object* v___x_1156_ = _args[0];
lean_object* v___x_1157_ = _args[1];
lean_object* v_stx_1158_ = _args[2];
lean_object* v___x_1159_ = _args[3];
lean_object* v___x_1160_ = _args[4];
lean_object* v___x_1161_ = _args[5];
lean_object* v___x_1162_ = _args[6];
lean_object* v___x_1163_ = _args[7];
lean_object* v___x_1164_ = _args[8];
lean_object* v___x_1165_ = _args[9];
lean_object* v_only_1166_ = _args[10];
lean_object* v___y_1167_ = _args[11];
lean_object* v___y_1168_ = _args[12];
lean_object* v___y_1169_ = _args[13];
lean_object* v___y_1170_ = _args[14];
lean_object* v___y_1171_ = _args[15];
lean_object* v___y_1172_ = _args[16];
lean_object* v___y_1173_ = _args[17];
lean_object* v___y_1174_ = _args[18];
lean_object* v___y_1175_ = _args[19];
_start:
{
uint8_t v___x_50423__boxed_1176_; lean_object* v_res_1177_; 
v___x_50423__boxed_1176_ = lean_unbox(v___x_1159_);
v_res_1177_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(v___x_1156_, v___x_1157_, v_stx_1158_, v___x_50423__boxed_1176_, v___x_1160_, v___x_1161_, v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_, v_only_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v_only_1166_);
lean_dec_ref(v___x_1156_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_1178_, size_t v_i_1179_, lean_object* v_bs_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1179_, v_sz_1178_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_bs_1180_);
return v___x_1182_;
}
else
{
lean_object* v_v_1183_; lean_object* v___x_1184_; lean_object* v_bs_x27_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
v_v_1183_ = lean_array_uget(v_bs_1180_, v_i_1179_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v_bs_x27_1185_ = lean_array_uset(v_bs_1180_, v_i_1179_, v___x_1184_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1179_, v___x_1186_);
v___x_1188_ = lean_array_uset(v_bs_x27_1185_, v_i_1179_, v_v_1183_);
v_i_1179_ = v___x_1187_;
v_bs_1180_ = v___x_1188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_bs_1192_){
_start:
{
size_t v_sz_boxed_1193_; size_t v_i_boxed_1194_; lean_object* v_res_1195_; 
v_sz_boxed_1193_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1194_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1193_, v_i_boxed_1194_, v_bs_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0));
v___x_1216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1));
v___x_1217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3));
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
lean_inc(v_stx_1205_);
v___x_1220_ = l_Lean_Syntax_isOfKind(v_stx_1205_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec(v_stx_1205_);
v___x_1221_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; size_t v_sz_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = l_Lean_Syntax_getArg(v_stx_1205_, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_getArgs(v___x_1223_);
lean_dec(v___x_1223_);
v_sz_1225_ = lean_array_size(v___x_1224_);
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1225_, v___x_1226_, v___x_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec(v_stx_1205_);
v___x_1228_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1278_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1231_ = v___x_1227_;
v_isShared_1232_ = v_isSharedCheck_1278_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1227_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1278_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v_only_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1233_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_unsigned_to_nat(2u);
v___x_1269_ = l_Lean_Syntax_getArg(v_stx_1205_, v___x_1268_);
v___x_1270_ = l_Lean_Syntax_isNone(v___x_1269_);
if (v___x_1270_ == 0)
{
uint8_t v___x_1271_; 
lean_inc(v___x_1269_);
v___x_1271_ = l_Lean_Syntax_matchesNull(v___x_1269_, v___x_1222_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec(v___x_1269_);
lean_del_object(v___x_1231_);
lean_dec(v_val_1229_);
lean_dec(v_stx_1205_);
v___x_1272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1272_;
}
else
{
lean_object* v_only_1273_; lean_object* v___x_1275_; 
v_only_1273_ = l_Lean_Syntax_getArg(v___x_1269_, v___x_1234_);
lean_dec(v___x_1269_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_only_1273_);
v___x_1275_ = v___x_1231_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_only_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v_only_1251_ = v___x_1275_;
v___y_1252_ = v_a_1206_;
v___y_1253_ = v_a_1207_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
goto v___jp_1250_;
}
}
}
else
{
lean_object* v___x_1277_; 
lean_dec(v___x_1269_);
lean_del_object(v___x_1231_);
v___x_1277_ = lean_box(0);
v_only_1251_ = v___x_1277_;
v___y_1252_ = v_a_1206_;
v___y_1253_ = v_a_1207_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
goto v___jp_1250_;
}
v___jp_1235_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; 
v___x_1246_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1245_);
lean_dec_ref(v___y_1245_);
v___x_1247_ = lean_box(v___x_1220_);
v___f_1248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1248_, 0, v___x_1246_);
lean_closure_set(v___f_1248_, 1, v___x_1222_);
lean_closure_set(v___f_1248_, 2, v_stx_1205_);
lean_closure_set(v___f_1248_, 3, v___x_1247_);
lean_closure_set(v___f_1248_, 4, v___x_1233_);
lean_closure_set(v___f_1248_, 5, v___x_1234_);
lean_closure_set(v___f_1248_, 6, v___x_1215_);
lean_closure_set(v___f_1248_, 7, v___x_1216_);
lean_closure_set(v___f_1248_, 8, v___x_1217_);
lean_closure_set(v___f_1248_, 9, v___x_1218_);
lean_closure_set(v___f_1248_, 10, v___y_1236_);
v___x_1249_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_1229_, v___f_1248_, v___y_1242_, v___y_1241_, v___y_1243_, v___y_1238_, v___y_1240_, v___y_1237_, v___y_1244_, v___y_1239_);
return v___x_1249_;
}
v___jp_1250_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(3u);
v___x_1261_ = l_Lean_Syntax_getArg(v_stx_1205_, v___x_1260_);
v___x_1262_ = l_Lean_Syntax_isNone(v___x_1261_);
if (v___x_1262_ == 0)
{
uint8_t v___x_1263_; 
lean_inc(v___x_1261_);
v___x_1263_ = l_Lean_Syntax_matchesNull(v___x_1261_, v___x_1260_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec(v___x_1261_);
lean_dec(v_only_1251_);
lean_dec(v_val_1229_);
lean_dec(v_stx_1205_);
v___x_1264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v_params_x3f_1266_; 
v___x_1265_ = l_Lean_Syntax_getArg(v___x_1261_, v___x_1222_);
lean_dec(v___x_1261_);
v_params_x3f_1266_ = l_Lean_Syntax_getArgs(v___x_1265_);
lean_dec(v___x_1265_);
v___y_1236_ = v_only_1251_;
v___y_1237_ = v___y_1257_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1259_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1252_;
v___y_1243_ = v___y_1254_;
v___y_1244_ = v___y_1258_;
v___y_1245_ = v_params_x3f_1266_;
goto v___jp_1235_;
}
}
else
{
lean_object* v___x_1267_; 
lean_dec(v___x_1261_);
v___x_1267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___y_1236_ = v_only_1251_;
v___y_1237_ = v___y_1257_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1259_;
v___y_1240_ = v___y_1256_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1252_;
v___y_1243_ = v___y_1254_;
v___y_1244_ = v___y_1258_;
v___y_1245_ = v___x_1267_;
goto v___jp_1235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object* v_00_u03b1_1290_, lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_1291_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(v_00_u03b1_1303_, v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object* v_ref_1316_, lean_object* v_msgData_1317_, uint8_t v_severity_1318_, uint8_t v_isSilent_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_1316_, v_msgData_1317_, v_severity_1318_, v_isSilent_1319_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1331_, lean_object* v_msgData_1332_, lean_object* v_severity_1333_, lean_object* v_isSilent_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v_severity_boxed_1345_; uint8_t v_isSilent_boxed_1346_; lean_object* v_res_1347_; 
v_severity_boxed_1345_ = lean_unbox(v_severity_1333_);
v_isSilent_boxed_1346_ = lean_unbox(v_isSilent_1334_);
v_res_1347_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(v_ref_1331_, v_msgData_1332_, v_severity_boxed_1345_, v_isSilent_boxed_1346_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v_ref_1331_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1388_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_1390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14));
v___x_1391_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_1392_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1388_, v___x_1389_, v___x_1390_, v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_1394_;
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
