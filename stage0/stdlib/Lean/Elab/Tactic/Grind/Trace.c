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
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_symSimpMethods_20_; lean_object* v_symDSimpMethods_21_; lean_object* v_anchorRefs_x3f_22_; uint8_t v_cheapCases_23_; uint8_t v_reportMVarIssue_24_; lean_object* v_splitSource_25_; lean_object* v_ematchDiagSource_26_; lean_object* v_symPrios_27_; lean_object* v_extensions_28_; uint8_t v_debug_29_; uint8_t v_ematchDiag_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_genLocal_38_; lean_object* v_instances_39_; uint8_t v_matchEqs_40_; uint8_t v_splitMatch_41_; uint8_t v_splitIte_42_; uint8_t v_splitIndPred_43_; uint8_t v_splitImp_44_; lean_object* v_canonHeartbeats_45_; uint8_t v_ext_46_; uint8_t v_extAll_47_; uint8_t v_etaStruct_48_; uint8_t v_funext_49_; uint8_t v_lookahead_50_; uint8_t v_verbose_51_; uint8_t v_clean_52_; uint8_t v_qlia_53_; uint8_t v_mbtc_54_; uint8_t v_zetaDelta_55_; uint8_t v_zeta_56_; uint8_t v_distrib_57_; lean_object* v_maxChar_58_; uint8_t v_ring_59_; lean_object* v_ringSteps_60_; lean_object* v_ringMaxDegree_61_; uint8_t v_linarith_62_; uint8_t v_lia_63_; lean_object* v_liaSteps_64_; uint8_t v_hom_65_; uint8_t v_ac_66_; lean_object* v_acSteps_67_; lean_object* v_exp_68_; uint8_t v_abstractProof_69_; uint8_t v_inj_70_; uint8_t v_order_71_; lean_object* v_min_72_; lean_object* v_detailed_73_; uint8_t v_useSorry_74_; uint8_t v_revert_75_; uint8_t v_funCC_76_; uint8_t v_reducible_77_; lean_object* v_maxSuggestions_78_; uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
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
v_markInstances_31_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 1);
v_lax_32_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 2);
v_suggestions_33_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 3);
v_locals_34_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 4);
v_splits_35_ = lean_ctor_get(v_config_12_, 0);
v_ematch_36_ = lean_ctor_get(v_config_12_, 1);
v_gen_37_ = lean_ctor_get(v_config_12_, 2);
v_genLocal_38_ = lean_ctor_get(v_config_12_, 3);
v_instances_39_ = lean_ctor_get(v_config_12_, 4);
v_matchEqs_40_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 5);
v_splitMatch_41_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 6);
v_splitIte_42_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 7);
v_splitIndPred_43_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 8);
v_splitImp_44_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 9);
v_canonHeartbeats_45_ = lean_ctor_get(v_config_12_, 5);
v_ext_46_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 10);
v_extAll_47_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 11);
v_etaStruct_48_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 12);
v_funext_49_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 13);
v_lookahead_50_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 14);
v_verbose_51_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 15);
v_clean_52_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 16);
v_qlia_53_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 17);
v_mbtc_54_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 18);
v_zetaDelta_55_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 19);
v_zeta_56_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 20);
v_distrib_57_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 21);
v_maxChar_58_ = lean_ctor_get(v_config_12_, 6);
v_ring_59_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 22);
v_ringSteps_60_ = lean_ctor_get(v_config_12_, 7);
v_ringMaxDegree_61_ = lean_ctor_get(v_config_12_, 8);
v_linarith_62_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 23);
v_lia_63_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 24);
v_liaSteps_64_ = lean_ctor_get(v_config_12_, 9);
v_hom_65_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 25);
v_ac_66_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 26);
v_acSteps_67_ = lean_ctor_get(v_config_12_, 10);
v_exp_68_ = lean_ctor_get(v_config_12_, 11);
v_abstractProof_69_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 27);
v_inj_70_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 28);
v_order_71_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 29);
v_min_72_ = lean_ctor_get(v_config_12_, 12);
v_detailed_73_ = lean_ctor_get(v_config_12_, 13);
v_useSorry_74_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 30);
v_revert_75_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 31);
v_funCC_76_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 32);
v_reducible_77_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*15 + 33);
v_maxSuggestions_78_ = lean_ctor_get(v_config_12_, 14);
v___x_79_ = 1;
lean_inc(v_maxSuggestions_78_);
lean_inc(v_detailed_73_);
lean_inc(v_min_72_);
lean_inc(v_exp_68_);
lean_inc(v_acSteps_67_);
lean_inc(v_liaSteps_64_);
lean_inc(v_ringMaxDegree_61_);
lean_inc(v_ringSteps_60_);
lean_inc(v_maxChar_58_);
lean_inc(v_canonHeartbeats_45_);
lean_inc(v_instances_39_);
lean_inc(v_genLocal_38_);
lean_inc(v_gen_37_);
lean_inc(v_ematch_36_);
lean_inc(v_splits_35_);
v___x_80_ = lean_alloc_ctor(0, 15, 34);
lean_ctor_set(v___x_80_, 0, v_splits_35_);
lean_ctor_set(v___x_80_, 1, v_ematch_36_);
lean_ctor_set(v___x_80_, 2, v_gen_37_);
lean_ctor_set(v___x_80_, 3, v_genLocal_38_);
lean_ctor_set(v___x_80_, 4, v_instances_39_);
lean_ctor_set(v___x_80_, 5, v_canonHeartbeats_45_);
lean_ctor_set(v___x_80_, 6, v_maxChar_58_);
lean_ctor_set(v___x_80_, 7, v_ringSteps_60_);
lean_ctor_set(v___x_80_, 8, v_ringMaxDegree_61_);
lean_ctor_set(v___x_80_, 9, v_liaSteps_64_);
lean_ctor_set(v___x_80_, 10, v_acSteps_67_);
lean_ctor_set(v___x_80_, 11, v_exp_68_);
lean_ctor_set(v___x_80_, 12, v_min_72_);
lean_ctor_set(v___x_80_, 13, v_detailed_73_);
lean_ctor_set(v___x_80_, 14, v_maxSuggestions_78_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15, v___x_79_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 1, v_markInstances_31_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 2, v_lax_32_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 3, v_suggestions_33_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 4, v_locals_34_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 5, v_matchEqs_40_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 6, v_splitMatch_41_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 7, v_splitIte_42_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 8, v_splitIndPred_43_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 9, v_splitImp_44_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 10, v_ext_46_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 11, v_extAll_47_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 12, v_etaStruct_48_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 13, v_funext_49_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 14, v_lookahead_50_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 15, v_verbose_51_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 16, v_clean_52_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 17, v_qlia_53_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 18, v_mbtc_54_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 19, v_zetaDelta_55_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 20, v_zeta_56_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 21, v_distrib_57_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 22, v_ring_59_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 23, v_linarith_62_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 24, v_lia_63_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 25, v_hom_65_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 26, v_ac_66_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 27, v_abstractProof_69_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 28, v_inj_70_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 29, v_order_71_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 30, v_useSorry_74_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 31, v_revert_75_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 32, v_funCC_76_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*15 + 33, v_reducible_77_);
lean_inc_ref(v_extensions_28_);
lean_inc_ref(v_symPrios_27_);
lean_inc(v_ematchDiagSource_26_);
lean_inc(v_splitSource_25_);
lean_inc(v_anchorRefs_x3f_22_);
lean_inc_ref(v_symDSimpMethods_21_);
lean_inc_ref(v_symSimpMethods_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_81_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_81_, 0, v_simp_18_);
lean_ctor_set(v___x_81_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_81_, 2, v_symSimpMethods_20_);
lean_ctor_set(v___x_81_, 3, v_symDSimpMethods_21_);
lean_ctor_set(v___x_81_, 4, v___x_80_);
lean_ctor_set(v___x_81_, 5, v_anchorRefs_x3f_22_);
lean_ctor_set(v___x_81_, 6, v_splitSource_25_);
lean_ctor_set(v___x_81_, 7, v_ematchDiagSource_26_);
lean_ctor_set(v___x_81_, 8, v_symPrios_27_);
lean_ctor_set(v___x_81_, 9, v_extensions_28_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*10, v_cheapCases_23_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*10 + 1, v_reportMVarIssue_24_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*10 + 2, v_debug_29_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*10 + 3, v_ematchDiag_30_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_82_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_82_, 0, v_toContext_13_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
lean_ctor_set(v___x_82_, 2, v_sctx_14_);
lean_ctor_set(v___x_82_, 3, v_methods_15_);
lean_ctor_set(v___x_82_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_83_ = lean_apply_9(v_x_1_, v___x_82_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_107_, lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_107_, v_x_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object* v_opts_119_, lean_object* v_opt_120_){
_start:
{
lean_object* v_name_121_; lean_object* v_defValue_122_; lean_object* v_map_123_; lean_object* v___x_124_; 
v_name_121_ = lean_ctor_get(v_opt_120_, 0);
v_defValue_122_ = lean_ctor_get(v_opt_120_, 1);
v_map_123_ = lean_ctor_get(v_opts_119_, 0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_123_, v_name_121_);
if (lean_obj_tag(v___x_124_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = lean_unbox(v_defValue_122_);
return v___x_125_;
}
else
{
lean_object* v_val_126_; 
v_val_126_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v___x_124_, 1);
if (lean_obj_tag(v_val_126_) == 1)
{
uint8_t v_v_127_; 
v_v_127_ = lean_ctor_get_uint8(v_val_126_, 0);
lean_dec_ref_known(v_val_126_, 0);
return v_v_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec(v_val_126_);
v___x_128_ = lean_unbox(v_defValue_122_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object* v_opts_129_, lean_object* v_opt_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v_opts_129_, v_opt_130_);
lean_dec_ref(v_opt_130_);
lean_dec_ref(v_opts_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Array_mkArray0___redArg();
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object* v_goal_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_seq_171_; lean_object* v_goal_172_; lean_object* v_seq_175_; uint8_t v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v_mvarId_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v_seq_240_; lean_object* v_goal_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_seq_175_ = lean_box(0);
v___x_285_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_167_);
v___x_286_ = l_Lean_Meta_tactic_hygienic;
v___x_287_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_285_, v___x_286_);
lean_dec_ref(v___x_285_);
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7));
lean_inc_ref(v_goal_159_);
v___x_289_ = l_Lean_Meta_Grind_Goal_intros(v_goal_159_, v___x_288_, v___x_287_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
if (lean_obj_tag(v_a_290_) == 1)
{
lean_object* v_goal_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_goal_159_);
v_goal_291_ = lean_ctor_get(v_a_290_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_a_290_, 0);
lean_dec(v_unused_320_);
v___x_293_ = v_a_290_;
v_isShared_294_ = v_isSharedCheck_319_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_goal_291_);
lean_dec(v_a_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_319_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_291_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_ref_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v_ref_297_ = lean_ctor_get(v_a_167_, 2);
v___x_298_ = 0;
v___x_299_ = l_Lean_SourceInfo_fromRef(v_ref_297_, v___x_298_);
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9));
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10));
lean_inc(v___x_299_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 2);
lean_ctor_set(v___x_293_, 1, v___x_301_);
lean_ctor_set(v___x_293_, 0, v___x_299_);
v___x_303_ = v___x_293_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_310_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12));
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13);
lean_inc(v___x_299_);
v___x_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_299_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_305_);
v___x_307_ = l_Lean_Syntax_node2(v___x_299_, v___x_300_, v___x_303_, v___x_306_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_seq_175_);
v___x_309_ = l_List_appendTR___redArg(v_seq_175_, v___x_308_);
v_seq_240_ = v___x_309_;
v_goal_241_ = v_a_296_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
v___y_250_ = v_a_168_;
goto v___jp_239_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_del_object(v___x_293_);
v_a_311_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_295_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_295_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_dec(v_a_290_);
v_seq_240_ = v_seq_175_;
v_goal_241_ = v_goal_159_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
v___y_250_ = v_a_168_;
goto v___jp_239_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_goal_159_);
v_a_321_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_289_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_289_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
v___jp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_seq_171_);
lean_ctor_set(v___x_173_, 1, v_goal_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
v___jp_176_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_MVarId_byContra_x3f(v_mvarId_181_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
if (lean_obj_tag(v_a_192_) == 1)
{
lean_object* v_val_193_; lean_object* v___x_194_; 
lean_dec_ref(v___y_179_);
v_val_193_ = lean_ctor_get(v_a_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_a_192_, 1);
v___x_194_ = l_Lean_Meta_intro1Core(v_val_193_, v___y_177_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v_snd_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_221_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v_snd_196_ = lean_ctor_get(v_a_195_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_a_195_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v_a_195_, 0);
lean_dec(v_unused_222_);
v___x_198_ = v_a_195_;
v_isShared_199_ = v_isSharedCheck_221_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_snd_196_);
lean_dec(v_a_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_221_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___y_178_);
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___y_178_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_196_);
v___x_201_ = v_reuseFailAlloc_220_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Meta_Grind_Goal_internalizeAll(v___x_201_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_ref_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_ref_204_ = lean_ctor_get(v___y_189_, 2);
v___x_205_ = l_Lean_SourceInfo_fromRef(v_ref_204_, v___y_177_);
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5));
v___x_207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6));
lean_inc(v___x_205_);
v___x_208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = l_Lean_Syntax_node1(v___x_205_, v___x_206_, v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_seq_175_);
v___x_211_ = l_List_appendTR___redArg(v___y_180_, v___x_210_);
v_seq_171_ = v___x_211_;
v_goal_172_ = v_a_203_;
goto v___jp_170_;
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___y_180_);
v_a_212_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_202_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_202_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v___y_180_);
lean_dec_ref(v___y_178_);
v_a_223_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_194_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_194_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_dec(v_a_192_);
lean_dec_ref(v___y_178_);
v_seq_171_ = v___y_180_;
v_goal_172_ = v___y_179_;
goto v___jp_170_;
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec_ref(v___y_178_);
v_a_231_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_191_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_191_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
v___jp_239_:
{
lean_object* v_toGoalState_251_; lean_object* v_mvarId_252_; lean_object* v___x_253_; 
v_toGoalState_251_ = lean_ctor_get(v_goal_241_, 0);
v_mvarId_252_ = lean_ctor_get(v_goal_241_, 1);
lean_inc(v_mvarId_252_);
v___x_253_ = l_Lean_MVarId_getType(v_mvarId_252_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; uint8_t v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_n(v_a_254_, 2);
lean_dec_ref_known(v___x_253_, 1);
v___x_255_ = l_Lean_Expr_isFalse(v_a_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_inc_ref(v_toGoalState_251_);
v___x_256_ = l_Lean_Meta_isProp(v_a_254_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; uint8_t v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = lean_unbox(v_a_257_);
lean_dec(v_a_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_inc(v_mvarId_252_);
v___x_259_ = l_Lean_MVarId_exfalso(v_mvarId_252_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v___y_177_ = v___x_255_;
v___y_178_ = v_toGoalState_251_;
v___y_179_ = v_goal_241_;
v___y_180_ = v_seq_240_;
v_mvarId_181_ = v_a_260_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
v___y_190_ = v___y_250_;
goto v___jp_176_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_toGoalState_251_);
lean_dec_ref(v_goal_241_);
lean_dec(v_seq_240_);
v_a_261_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_inc(v_mvarId_252_);
v___y_177_ = v___x_255_;
v___y_178_ = v_toGoalState_251_;
v___y_179_ = v_goal_241_;
v___y_180_ = v_seq_240_;
v_mvarId_181_ = v_mvarId_252_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
v___y_190_ = v___y_250_;
goto v___jp_176_;
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_toGoalState_251_);
lean_dec_ref(v_goal_241_);
lean_dec(v_seq_240_);
v_a_269_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_256_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_256_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_dec(v_a_254_);
v_seq_171_ = v_seq_240_;
v_goal_172_ = v_goal_241_;
goto v___jp_170_;
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref(v_goal_241_);
lean_dec(v_seq_240_);
v_a_277_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_253_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_253_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object* v_goal_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_goal_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object* v_msgData_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_env_378_; uint8_t v___x_379_; lean_object* v_env_380_; lean_object* v___x_381_; lean_object* v_toCold_382_; lean_object* v_mctx_383_; lean_object* v_lctx_384_; lean_object* v_options_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_377_ = lean_st_ref_get(v___y_375_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_env_378_);
lean_dec(v___x_377_);
v___x_379_ = 0;
v_env_380_ = l_Lean_Environment_setRecordingDeps(v_env_378_, v___x_379_);
v___x_381_ = lean_st_ref_get(v___y_373_);
v_toCold_382_ = lean_ctor_get(v___y_374_, 0);
v_mctx_383_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_mctx_383_);
lean_dec(v___x_381_);
v_lctx_384_ = lean_ctor_get(v___y_372_, 2);
v_options_385_ = lean_ctor_get(v_toCold_382_, 2);
lean_inc_ref(v_options_385_);
lean_inc_ref(v_lctx_384_);
v___x_386_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_386_, 0, v_env_380_);
lean_ctor_set(v___x_386_, 1, v_mctx_383_);
lean_ctor_set(v___x_386_, 2, v_lctx_384_);
lean_ctor_set(v___x_386_, 3, v_options_385_);
v___x_387_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_msgData_371_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object* v_msgData_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msgData_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_ref_402_ = lean_ctor_get(v___y_399_, 2);
v___x_403_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_inc(v_ref_402_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_ref_402_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 1)
{
lean_object* v_pre_429_; 
v_pre_429_ = lean_ctor_get(v_x_428_, 0);
switch(lean_obj_tag(v_pre_429_))
{
case 1:
{
lean_object* v_pre_430_; 
v_pre_430_ = lean_ctor_get(v_pre_429_, 0);
switch(lean_obj_tag(v_pre_430_))
{
case 0:
{
lean_object* v_str_431_; lean_object* v_str_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_str_431_ = lean_ctor_get(v_x_428_, 1);
v_str_432_ = lean_ctor_get(v_pre_429_, 1);
v___x_433_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_434_ = lean_string_dec_eq(v_str_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_436_ = lean_string_dec_eq(v_str_432_, v___x_435_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_438_ = lean_string_dec_eq(v_str_431_, v___x_437_);
if (v___x_438_ == 0)
{
return v___x_438_;
}
else
{
return v_suppressElabErrors_427_;
}
}
}
else
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_440_ = lean_string_dec_eq(v_str_431_, v___x_439_);
if (v___x_440_ == 0)
{
return v___x_440_;
}
else
{
return v_suppressElabErrors_427_;
}
}
}
case 1:
{
lean_object* v_pre_441_; 
v_pre_441_ = lean_ctor_get(v_pre_430_, 0);
if (lean_obj_tag(v_pre_441_) == 0)
{
lean_object* v_str_442_; lean_object* v_str_443_; lean_object* v_str_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_str_442_ = lean_ctor_get(v_x_428_, 1);
v_str_443_ = lean_ctor_get(v_pre_429_, 1);
v_str_444_ = lean_ctor_get(v_pre_430_, 1);
v___x_445_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_446_ = lean_string_dec_eq(v_str_444_, v___x_445_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_448_ = lean_string_dec_eq(v_str_443_, v___x_447_);
if (v___x_448_ == 0)
{
return v___x_448_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_450_ = lean_string_dec_eq(v_str_442_, v___x_449_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
return v_suppressElabErrors_427_;
}
}
}
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 0;
return v___x_451_;
}
}
default: 
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
}
}
case 0:
{
lean_object* v_str_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_str_453_ = lean_ctor_get(v_x_428_, 1);
v___x_454_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_455_ = lean_string_dec_eq(v_str_453_, v___x_454_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
return v_suppressElabErrors_427_;
}
}
default: 
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_458_, lean_object* v_x_459_){
_start:
{
uint8_t v_suppressElabErrors_boxed_460_; uint8_t v_res_461_; lean_object* v_r_462_; 
v_suppressElabErrors_boxed_460_ = lean_unbox(v_suppressElabErrors_458_);
v_res_461_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_460_, v_x_459_);
lean_dec(v_x_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_464_, lean_object* v_msgData_465_, uint8_t v_severity_466_, uint8_t v_isSilent_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v_toCold_481_; lean_object* v___y_482_; lean_object* v___y_511_; lean_object* v___y_512_; uint8_t v___y_513_; uint8_t v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; lean_object* v___y_518_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; lean_object* v___y_544_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___x_559_; uint8_t v___y_561_; uint8_t v___x_567_; 
v___x_559_ = 2;
v___x_567_ = l_Lean_instBEqMessageSeverity_beq(v_severity_466_, v___x_559_);
if (v___x_567_ == 0)
{
v___y_561_ = v___x_567_;
goto v___jp_560_;
}
else
{
uint8_t v___x_568_; 
lean_inc_ref(v_msgData_465_);
v___x_568_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_465_);
if (v___x_568_ == 0)
{
v___y_561_ = v___x_568_;
goto v___jp_560_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec_ref(v_msgData_465_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
v___jp_473_:
{
lean_object* v_currNamespace_483_; lean_object* v_openDecls_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_env_489_; lean_object* v_nextMacroScope_490_; lean_object* v_ngen_491_; lean_object* v_auxDeclNGen_492_; lean_object* v_traceState_493_; lean_object* v_cache_494_; lean_object* v_recordedDeps_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_509_; 
v_currNamespace_483_ = lean_ctor_get(v_toCold_481_, 4);
v_openDecls_484_ = lean_ctor_get(v_toCold_481_, 5);
lean_inc(v_openDecls_484_);
lean_inc(v_currNamespace_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_currNamespace_483_);
lean_ctor_set(v___x_485_, 1, v_openDecls_484_);
v___x_486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___y_477_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_478_);
v___x_487_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_487_, 0, v___y_478_);
lean_ctor_set(v___x_487_, 1, v___y_476_);
lean_ctor_set(v___x_487_, 2, v___y_475_);
lean_ctor_set(v___x_487_, 3, v___y_479_);
lean_ctor_set(v___x_487_, 4, v___x_486_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5, v___y_474_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5 + 1, v___y_480_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*5 + 2, v_isSilent_467_);
v___x_488_ = lean_st_ref_take(v___y_482_);
v_env_489_ = lean_ctor_get(v___x_488_, 0);
v_nextMacroScope_490_ = lean_ctor_get(v___x_488_, 1);
v_ngen_491_ = lean_ctor_get(v___x_488_, 2);
v_auxDeclNGen_492_ = lean_ctor_get(v___x_488_, 3);
v_traceState_493_ = lean_ctor_get(v___x_488_, 4);
v_cache_494_ = lean_ctor_get(v___x_488_, 5);
v_recordedDeps_495_ = lean_ctor_get(v___x_488_, 6);
v_messages_496_ = lean_ctor_get(v___x_488_, 7);
v_infoState_497_ = lean_ctor_get(v___x_488_, 8);
v_snapshotTasks_498_ = lean_ctor_get(v___x_488_, 9);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_509_ == 0)
{
v___x_500_ = v___x_488_;
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_recordedDeps_495_);
lean_inc(v_cache_494_);
lean_inc(v_traceState_493_);
lean_inc(v_auxDeclNGen_492_);
lean_inc(v_ngen_491_);
lean_inc(v_nextMacroScope_490_);
lean_inc(v_env_489_);
lean_dec(v___x_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = lean_box(0);
v___x_503_ = l_Lean_MessageLog_add(v___x_487_, v_messages_496_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 7, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_env_489_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_490_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_ngen_491_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_492_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_traceState_493_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v_cache_494_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_recordedDeps_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 9, v_snapshotTasks_498_);
v___x_505_ = v_reuseFailAlloc_508_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_st_ref_put(v___y_482_, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_502_);
return v___x_507_;
}
}
}
v___jp_510_:
{
lean_object* v_fileName_519_; lean_object* v_fileMap_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_536_; 
v_fileName_519_ = lean_ctor_get(v___y_515_, 0);
v_fileMap_520_ = lean_ctor_get(v___y_515_, 1);
v___x_521_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_465_);
v___x_522_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v___x_521_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_536_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_536_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc_ref_n(v_fileMap_520_, 2);
v___x_527_ = l_Lean_FileMap_toPosition(v_fileMap_520_, v___y_516_);
lean_dec(v___y_516_);
v___x_528_ = l_Lean_FileMap_toPosition(v_fileMap_520_, v___y_518_);
lean_dec(v___y_518_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0));
if (v___y_514_ == 0)
{
lean_del_object(v___x_525_);
lean_dec_ref(v___y_512_);
v___y_474_ = v___y_513_;
v___y_475_ = v___x_529_;
v___y_476_ = v___x_527_;
v___y_477_ = v_a_523_;
v___y_478_ = v_fileName_519_;
v___y_479_ = v___x_530_;
v___y_480_ = v___y_517_;
v_toCold_481_ = v___y_511_;
v___y_482_ = v___y_471_;
goto v___jp_473_;
}
else
{
uint8_t v___x_531_; 
lean_inc(v_a_523_);
v___x_531_ = l_Lean_MessageData_hasTag(v___y_512_, v_a_523_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec_ref_known(v___x_529_, 1);
lean_dec_ref(v___x_527_);
lean_dec(v_a_523_);
v___x_532_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_532_);
v___x_534_ = v___x_525_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_del_object(v___x_525_);
v___y_474_ = v___y_513_;
v___y_475_ = v___x_529_;
v___y_476_ = v___x_527_;
v___y_477_ = v_a_523_;
v___y_478_ = v_fileName_519_;
v___y_479_ = v___x_530_;
v___y_480_ = v___y_517_;
v_toCold_481_ = v___y_511_;
v___y_482_ = v___y_471_;
goto v___jp_473_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_541_);
lean_dec(v___y_542_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_inc(v___y_544_);
v___y_511_ = v___y_538_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_541_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_538_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_543_;
v___y_518_ = v___y_544_;
goto v___jp_510_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___y_511_ = v___y_538_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_541_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_538_;
v___y_516_ = v___y_544_;
v___y_517_ = v___y_543_;
v___y_518_ = v_val_546_;
goto v___jp_510_;
}
}
v___jp_547_:
{
lean_object* v_toCold_550_; lean_object* v_ref_551_; uint8_t v_suppressElabErrors_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v_ref_555_; lean_object* v___x_556_; 
v_toCold_550_ = lean_ctor_get(v___y_470_, 0);
v_ref_551_ = lean_ctor_get(v___y_470_, 2);
v_suppressElabErrors_552_ = lean_ctor_get_uint8(v___y_470_, sizeof(void*)*3 + 2);
v___x_553_ = lean_box(v_suppressElabErrors_552_);
v___f_554_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_554_, 0, v___x_553_);
v_ref_555_ = l_Lean_replaceRef(v_ref_464_, v_ref_551_);
v___x_556_ = l_Lean_Syntax_getPos_x3f(v_ref_555_, v___y_548_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___y_538_ = v_toCold_550_;
v___y_539_ = v_suppressElabErrors_552_;
v___y_540_ = v___f_554_;
v___y_541_ = v___y_548_;
v___y_542_ = v_ref_555_;
v___y_543_ = v___y_549_;
v___y_544_ = v___x_557_;
goto v___jp_537_;
}
else
{
lean_object* v_val_558_; 
v_val_558_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_556_, 1);
v___y_538_ = v_toCold_550_;
v___y_539_ = v_suppressElabErrors_552_;
v___y_540_ = v___f_554_;
v___y_541_ = v___y_548_;
v___y_542_ = v_ref_555_;
v___y_543_ = v___y_549_;
v___y_544_ = v_val_558_;
goto v___jp_537_;
}
}
v___jp_560_:
{
uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 1;
v___x_563_ = l_Lean_instBEqMessageSeverity_beq(v_severity_466_, v___x_562_);
if (v___x_563_ == 0)
{
v___y_548_ = v___y_561_;
v___y_549_ = v_severity_466_;
goto v___jp_547_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_470_);
v___x_565_ = l_Lean_warningAsError;
v___x_566_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_564_, v___x_565_);
lean_dec_ref(v___x_564_);
if (v___x_566_ == 0)
{
v___y_548_ = v___y_561_;
v___y_549_ = v_severity_466_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___y_561_;
v___y_549_ = v___x_559_;
goto v___jp_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_571_, lean_object* v_msgData_572_, lean_object* v_severity_573_, lean_object* v_isSilent_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v_severity_boxed_580_; uint8_t v_isSilent_boxed_581_; lean_object* v_res_582_; 
v_severity_boxed_580_ = lean_unbox(v_severity_573_);
v_isSilent_boxed_581_ = lean_unbox(v_isSilent_574_);
v_res_582_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_571_, v_msgData_572_, v_severity_boxed_580_, v_isSilent_boxed_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v_ref_571_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_583_, uint8_t v_severity_584_, uint8_t v_isSilent_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_ref_596_; lean_object* v___x_597_; 
v_ref_596_ = lean_ctor_get(v___y_593_, 2);
v___x_597_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_596_, v_msgData_583_, v_severity_584_, v_isSilent_585_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_598_, lean_object* v_severity_599_, lean_object* v_isSilent_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_severity_boxed_611_; uint8_t v_isSilent_boxed_612_; lean_object* v_res_613_; 
v_severity_boxed_611_ = lean_unbox(v_severity_599_);
v_isSilent_boxed_612_ = lean_unbox(v_isSilent_600_);
v_res_613_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_598_, v_severity_boxed_611_, v_isSilent_boxed_612_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_msgData_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; 
v___x_625_ = 1;
v___x_626_ = 0;
v___x_627_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_614_, v___x_625_, v___x_626_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_msgData_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_msgData_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
return v_res_639_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v___x_658_, lean_object* v_stx_659_, uint8_t v___x_660_, lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v_a_670_, lean_object* v_params_671_, lean_object* v_____x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_suggestions_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_906_; 
v_fst_734_ = lean_ctor_get(v_____x_672_, 0);
v_snd_735_ = lean_ctor_get(v_____x_672_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_____x_672_);
if (v_isSharedCheck_906_ == 0)
{
v___x_737_ = v_____x_672_;
v_isShared_738_ = v_isSharedCheck_906_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_734_);
lean_dec(v_____x_672_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_906_;
goto v_resetjp_736_;
}
v___jp_683_:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_array_get_size(v_suggestions_684_);
v___x_688_ = lean_nat_dec_eq(v___x_687_, v___x_658_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_box(0);
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_691_ = 4;
v___x_692_ = l_Lean_MessageData_nil;
v___x_693_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_659_, v_suggestions_684_, v___x_689_, v___x_690_, v___x_689_, v___x_691_, v___x_692_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_693_, 0);
lean_dec(v_unused_702_);
v___x_695_ = v___x_693_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_dec(v___x_693_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_box(v___x_660_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_693_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_711_ = lean_array_get(v___x_661_, v_suggestions_684_, v___x_662_);
lean_dec_ref(v_suggestions_684_);
v___x_712_ = lean_box(0);
v___x_713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_714_ = 4;
v___x_715_ = l_Lean_MessageData_nil;
v___x_716_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_659_, v___x_711_, v___x_712_, v___x_713_, v___x_712_, v___x_714_, v___x_715_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_725_);
v___x_718_ = v___x_716_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_box(v___x_660_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_716_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_716_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
v_resetjp_736_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_Grind_Action_run(v_snd_735_, v_a_663_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
if (lean_obj_tag(v_a_740_) == 0)
{
lean_object* v_seq_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_848_; 
v_seq_741_ = lean_ctor_get(v_a_740_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_848_ == 0)
{
v___x_743_ = v_a_740_;
v_isShared_744_ = v_isSharedCheck_848_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_seq_741_);
lean_dec(v_a_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_848_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_List_appendTR___redArg(v_fst_734_, v_seq_741_);
lean_inc(v___x_745_);
v___x_746_ = l_Lean_Meta_Grind_mkFinishTactic(v___x_745_, v_a_664_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v_suggestions_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_suggestions_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___x_831_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
lean_inc_n(v___x_745_, 2);
v___x_748_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v___x_745_);
v___x_808_ = lean_mk_empty_array_with_capacity(v___x_662_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_a_670_);
lean_inc_ref(v_a_665_);
lean_inc_ref(v___x_809_);
v___x_831_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_809_, v_a_665_, v___x_745_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; uint8_t v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = lean_unbox(v_a_832_);
lean_dec(v_a_832_);
if (v___x_833_ == 0)
{
v_suggestions_811_ = v___x_808_;
v___y_812_ = v___y_673_;
v___y_813_ = v___y_674_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
goto v___jp_810_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
lean_inc_ref(v___x_669_);
lean_inc_ref(v___x_668_);
lean_inc_ref(v___x_667_);
lean_inc_ref(v___x_666_);
v___x_835_ = l_Lean_Name_mkStr5(v___x_666_, v___x_667_, v___x_668_, v___x_669_, v___x_834_);
lean_inc(v___x_748_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_748_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
lean_ctor_set(v___x_838_, 2, v___x_837_);
lean_ctor_set(v___x_838_, 3, v___x_837_);
lean_ctor_set(v___x_838_, 4, v___x_837_);
lean_ctor_set(v___x_838_, 5, v___x_837_);
v___x_839_ = lean_array_push(v___x_808_, v___x_838_);
v_suggestions_811_ = v___x_839_;
v___y_812_ = v___y_673_;
v___y_813_ = v___y_674_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
goto v___jp_810_;
}
}
else
{
lean_dec_ref_known(v___x_809_, 1);
lean_dec_ref(v___x_808_);
lean_dec(v___x_748_);
lean_dec(v_a_747_);
lean_dec(v___x_745_);
lean_del_object(v___x_743_);
lean_del_object(v___x_737_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
return v___x_831_;
}
v___jp_749_:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_suggestions_750_);
v___x_761_ = lean_nat_dec_eq(v___x_760_, v___x_662_);
if (v___x_761_ == 0)
{
lean_dec(v___x_748_);
lean_dec(v___x_745_);
lean_del_object(v___x_743_);
lean_del_object(v___x_737_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
v_suggestions_684_ = v_suggestions_750_;
v___y_685_ = v___y_758_;
v___y_686_ = v___y_759_;
goto v___jp_683_;
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v_suggestions_750_);
v___x_762_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v___x_745_, v___y_758_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_mvarId_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_798_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_mvarId_764_ = lean_ctor_get(v_a_665_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_665_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_a_665_, 0);
lean_dec(v_unused_799_);
v___x_766_ = v_a_665_;
v_isShared_767_ = v_isSharedCheck_798_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_mvarId_764_);
lean_dec(v_a_665_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_798_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3);
v___x_769_ = l_Lean_MessageData_ofSyntax(v_a_763_);
v___x_770_ = l_Lean_indentD(v___x_769_);
if (v_isShared_767_ == 0)
{
lean_ctor_set_tag(v___x_766_, 7);
lean_ctor_set(v___x_766_, 1, v___x_770_);
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_797_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 7);
lean_ctor_set(v___x_737_, 1, v___x_773_);
lean_ctor_set(v___x_737_, 0, v___x_772_);
v___x_775_ = v___x_737_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_796_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
lean_ctor_set(v___x_743_, 0, v_mvarId_764_);
v___x_777_ = v___x_743_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_mvarId_764_);
v___x_777_ = v_reuseFailAlloc_795_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_775_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v___x_778_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
v___x_781_ = l_Lean_Name_mkStr5(v___x_666_, v___x_667_, v___x_668_, v___x_669_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_748_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
lean_ctor_set(v___x_784_, 2, v___x_783_);
lean_ctor_set(v___x_784_, 3, v___x_783_);
lean_ctor_set(v___x_784_, 4, v___x_783_);
lean_ctor_set(v___x_784_, 5, v___x_783_);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_786_ = lean_array_push(v___x_785_, v___x_784_);
v_suggestions_684_ = v___x_786_;
v___y_685_ = v___y_758_;
v___y_686_ = v___y_759_;
goto v___jp_683_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v___x_748_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_stx_659_);
v_a_787_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_779_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_779_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
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
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v___x_748_);
lean_del_object(v___x_743_);
lean_del_object(v___x_737_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
v_a_800_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_762_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_762_);
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
}
v___jp_810_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
lean_inc(v_a_747_);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v_a_747_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
lean_inc_ref(v_a_665_);
v___x_823_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_809_, v_a_665_, v___x_822_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; uint8_t v___x_825_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = lean_unbox(v_a_824_);
lean_dec(v_a_824_);
if (v___x_825_ == 0)
{
lean_dec(v_a_747_);
v_suggestions_750_ = v_suggestions_811_;
v___y_751_ = v___y_812_;
v___y_752_ = v___y_813_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
goto v___jp_749_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8));
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_a_747_);
v___x_828_ = lean_box(0);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
lean_ctor_set(v___x_829_, 3, v___x_828_);
lean_ctor_set(v___x_829_, 4, v___x_828_);
lean_ctor_set(v___x_829_, 5, v___x_828_);
v___x_830_ = lean_array_push(v_suggestions_811_, v___x_829_);
v_suggestions_750_ = v___x_830_;
v___y_751_ = v___y_812_;
v___y_752_ = v___y_813_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
goto v___jp_749_;
}
}
else
{
lean_dec_ref(v_suggestions_811_);
lean_dec(v___x_748_);
lean_dec(v_a_747_);
lean_dec(v___x_745_);
lean_del_object(v___x_743_);
lean_del_object(v___x_737_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
return v___x_823_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v___x_745_);
lean_del_object(v___x_743_);
lean_del_object(v___x_737_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
v_a_840_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_746_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_746_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v_gs_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_737_);
lean_dec(v_fst_734_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
v_gs_849_ = lean_ctor_get(v_a_740_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_897_ == 0)
{
v___x_851_ = v_a_740_;
v_isShared_852_ = v_isSharedCheck_897_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_gs_849_);
lean_dec(v_a_740_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_897_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
if (lean_obj_tag(v_gs_849_) == 1)
{
lean_object* v_head_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_893_; 
v_head_853_ = lean_ctor_get(v_gs_849_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_gs_849_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_gs_849_, 1);
lean_dec(v_unused_894_);
v___x_855_ = v_gs_849_;
v_isShared_856_ = v_isSharedCheck_893_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_head_853_);
lean_dec(v_gs_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_893_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_head_853_);
v___x_858_ = v___x_851_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_head_853_);
v___x_858_ = v_reuseFailAlloc_892_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Grind_mkResult(v_params_671_, v___x_858_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_860_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10);
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 7);
lean_ctor_set(v___x_855_, 1, v_a_862_);
lean_ctor_set(v___x_855_, 0, v___x_863_);
v___x_865_ = v___x_855_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_862_);
v___x_865_ = v_reuseFailAlloc_875_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v___x_866_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_865_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_855_);
v_a_876_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_861_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_861_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_855_);
v_a_884_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_859_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_859_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_del_object(v___x_851_);
lean_dec(v_gs_849_);
v___x_895_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12);
v___x_896_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_895_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_737_);
lean_dec(v_fst_734_);
lean_dec_ref(v_a_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_stx_659_);
v_a_898_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_739_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_739_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v___x_907_ = _args[0];
lean_object* v_stx_908_ = _args[1];
lean_object* v___x_909_ = _args[2];
lean_object* v___x_910_ = _args[3];
lean_object* v___x_911_ = _args[4];
lean_object* v_a_912_ = _args[5];
lean_object* v_a_913_ = _args[6];
lean_object* v_a_914_ = _args[7];
lean_object* v___x_915_ = _args[8];
lean_object* v___x_916_ = _args[9];
lean_object* v___x_917_ = _args[10];
lean_object* v___x_918_ = _args[11];
lean_object* v_a_919_ = _args[12];
lean_object* v_params_920_ = _args[13];
lean_object* v_____x_921_ = _args[14];
lean_object* v___y_922_ = _args[15];
lean_object* v___y_923_ = _args[16];
lean_object* v___y_924_ = _args[17];
lean_object* v___y_925_ = _args[18];
lean_object* v___y_926_ = _args[19];
lean_object* v___y_927_ = _args[20];
lean_object* v___y_928_ = _args[21];
lean_object* v___y_929_ = _args[22];
lean_object* v___y_930_ = _args[23];
lean_object* v___y_931_ = _args[24];
_start:
{
uint8_t v___x_49627__boxed_932_; lean_object* v_res_933_; 
v___x_49627__boxed_932_ = lean_unbox(v___x_909_);
v_res_933_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v___x_907_, v_stx_908_, v___x_49627__boxed_932_, v___x_910_, v___x_911_, v_a_912_, v_a_913_, v_a_914_, v___x_915_, v___x_916_, v___x_917_, v___x_918_, v_a_919_, v_params_920_, v_____x_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v_params_920_);
lean_dec_ref(v_a_913_);
lean_dec(v___x_911_);
lean_dec_ref(v___x_910_);
lean_dec(v___x_907_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t v_sym_934_, lean_object* v_a_935_, lean_object* v___f_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
if (v_sym_934_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_box(0);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_a_935_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
v___x_949_ = lean_apply_11(v___f_936_, v___x_948_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, lean_box(0));
return v___x_949_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_a_935_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
v___x_952_ = lean_apply_11(v___f_936_, v_a_951_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, lean_box(0));
return v___x_952_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___f_936_);
v_a_953_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_950_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v_sym_961_, lean_object* v_a_962_, lean_object* v___f_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v_sym_boxed_974_; lean_object* v_res_975_; 
v_sym_boxed_974_ = lean_unbox(v_sym_961_);
v_res_975_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v_sym_boxed_974_, v_a_962_, v___f_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___y_976_, v___y_977_, v___y_978_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_998_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_998_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint8_t v___x_991_; 
v___x_991_ = lean_unbox(v_a_987_);
lean_dec(v_a_987_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_992_);
v___x_994_ = v___x_989_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_del_object(v___x_989_);
v___x_996_ = lean_box(0);
v___x_997_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_996_, v___y_978_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_997_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_986_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_986_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___x_1018_, lean_object* v___x_1019_, lean_object* v_stx_1020_, uint8_t v___x_1021_, lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v_a_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_ref_1040_; lean_object* v___x_1041_; 
v_ref_1040_ = lean_ctor_get(v___y_1037_, 2);
v___x_1041_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1018_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1032_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v_params_1045_; uint8_t v_sym_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___y_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v_params_1045_ = lean_ctor_get(v___y_1031_, 4);
v_sym_1046_ = lean_ctor_get_uint8(v___y_1031_, sizeof(void*)*5);
v___x_1047_ = lean_box(v___x_1021_);
lean_inc_ref(v_params_1045_);
v___f_1048_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 25, 14);
lean_closure_set(v___f_1048_, 0, v___x_1019_);
lean_closure_set(v___f_1048_, 1, v_stx_1020_);
lean_closure_set(v___f_1048_, 2, v___x_1047_);
lean_closure_set(v___f_1048_, 3, v___x_1022_);
lean_closure_set(v___f_1048_, 4, v___x_1023_);
lean_closure_set(v___f_1048_, 5, v_a_1042_);
lean_closure_set(v___f_1048_, 6, v_a_1024_);
lean_closure_set(v___f_1048_, 7, v_a_1025_);
lean_closure_set(v___f_1048_, 8, v___x_1026_);
lean_closure_set(v___f_1048_, 9, v___x_1027_);
lean_closure_set(v___f_1048_, 10, v___x_1028_);
lean_closure_set(v___f_1048_, 11, v___x_1029_);
lean_closure_set(v___f_1048_, 12, v_a_1030_);
lean_closure_set(v___f_1048_, 13, v_params_1045_);
v___x_1049_ = lean_box(v_sym_1046_);
v___y_1050_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 13, 3);
lean_closure_set(v___y_1050_, 0, v___x_1049_);
lean_closure_set(v___y_1050_, 1, v_a_1044_);
lean_closure_set(v___y_1050_, 2, v___f_1048_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1051_, 0, v___y_1050_);
v___x_1052_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1051_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v___y_1031_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1042_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v___x_1023_);
lean_dec_ref(v___x_1022_);
lean_dec(v_stx_1020_);
lean_dec(v___x_1019_);
v_a_1053_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1043_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1043_);
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
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v___x_1023_);
lean_dec_ref(v___x_1022_);
lean_dec(v_stx_1020_);
lean_dec(v___x_1019_);
v_a_1061_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1063_ = v___x_1041_;
v_isShared_1064_ = v_isSharedCheck_1072_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1041_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1072_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1065_ = lean_io_error_to_string(v_a_1061_);
v___x_1066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = l_Lean_MessageData_ofFormat(v___x_1066_);
lean_inc(v_ref_1040_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_ref_1040_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1068_);
v___x_1070_ = v___x_1063_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___x_1073_ = _args[0];
lean_object* v___x_1074_ = _args[1];
lean_object* v_stx_1075_ = _args[2];
lean_object* v___x_1076_ = _args[3];
lean_object* v___x_1077_ = _args[4];
lean_object* v___x_1078_ = _args[5];
lean_object* v_a_1079_ = _args[6];
lean_object* v_a_1080_ = _args[7];
lean_object* v___x_1081_ = _args[8];
lean_object* v___x_1082_ = _args[9];
lean_object* v___x_1083_ = _args[10];
lean_object* v___x_1084_ = _args[11];
lean_object* v_a_1085_ = _args[12];
lean_object* v___y_1086_ = _args[13];
lean_object* v___y_1087_ = _args[14];
lean_object* v___y_1088_ = _args[15];
lean_object* v___y_1089_ = _args[16];
lean_object* v___y_1090_ = _args[17];
lean_object* v___y_1091_ = _args[18];
lean_object* v___y_1092_ = _args[19];
lean_object* v___y_1093_ = _args[20];
lean_object* v___y_1094_ = _args[21];
_start:
{
uint8_t v___x_50298__boxed_1095_; lean_object* v_res_1096_; 
v___x_50298__boxed_1095_ = lean_unbox(v___x_1076_);
v_res_1096_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___x_1073_, v___x_1074_, v_stx_1075_, v___x_50298__boxed_1095_, v___x_1077_, v___x_1078_, v_a_1079_, v_a_1080_, v___x_1081_, v___x_1082_, v___x_1083_, v___x_1084_, v_a_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v_stx_1100_, uint8_t v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v_only_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v___x_1098_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1110_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0));
v___x_1123_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1122_, v___y_1109_, v___y_1110_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_params_1125_; uint8_t v___y_1127_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v_params_1125_ = lean_ctor_get(v___y_1109_, 4);
lean_inc_ref(v_params_1125_);
if (lean_obj_tag(v_only_1108_) == 0)
{
uint8_t v___x_1132_; 
v___x_1132_ = 0;
v___y_1127_ = v___x_1132_;
goto v___jp_1126_;
}
else
{
v___y_1127_ = v___x_1101_;
goto v___jp_1126_;
}
v___jp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_unsigned_to_nat(10000u);
v___x_1129_ = lean_box(v___x_1101_);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 22, 13);
lean_closure_set(v___f_1130_, 0, v___x_1128_);
lean_closure_set(v___f_1130_, 1, v___x_1099_);
lean_closure_set(v___f_1130_, 2, v_stx_1100_);
lean_closure_set(v___f_1130_, 3, v___x_1129_);
lean_closure_set(v___f_1130_, 4, v___x_1102_);
lean_closure_set(v___f_1130_, 5, v___x_1103_);
lean_closure_set(v___f_1130_, 6, v_a_1119_);
lean_closure_set(v___f_1130_, 7, v_a_1121_);
lean_closure_set(v___f_1130_, 8, v___x_1104_);
lean_closure_set(v___f_1130_, 9, v___x_1105_);
lean_closure_set(v___f_1130_, 10, v___x_1106_);
lean_closure_set(v___f_1130_, 11, v___x_1107_);
lean_closure_set(v___f_1130_, 12, v_a_1124_);
v___x_1131_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_1125_, v___x_1098_, v___y_1127_, v___f_1130_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v___y_1109_);
return v___x_1131_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1121_);
lean_dec(v_a_1119_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec(v_stx_1100_);
lean_dec(v___x_1099_);
v_a_1133_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1123_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1123_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1119_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec(v_stx_1100_);
lean_dec(v___x_1099_);
v_a_1141_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1120_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1120_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec(v_stx_1100_);
lean_dec(v___x_1099_);
v_a_1149_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1118_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1118_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object** _args){
lean_object* v___x_1157_ = _args[0];
lean_object* v___x_1158_ = _args[1];
lean_object* v_stx_1159_ = _args[2];
lean_object* v___x_1160_ = _args[3];
lean_object* v___x_1161_ = _args[4];
lean_object* v___x_1162_ = _args[5];
lean_object* v___x_1163_ = _args[6];
lean_object* v___x_1164_ = _args[7];
lean_object* v___x_1165_ = _args[8];
lean_object* v___x_1166_ = _args[9];
lean_object* v_only_1167_ = _args[10];
lean_object* v___y_1168_ = _args[11];
lean_object* v___y_1169_ = _args[12];
lean_object* v___y_1170_ = _args[13];
lean_object* v___y_1171_ = _args[14];
lean_object* v___y_1172_ = _args[15];
lean_object* v___y_1173_ = _args[16];
lean_object* v___y_1174_ = _args[17];
lean_object* v___y_1175_ = _args[18];
lean_object* v___y_1176_ = _args[19];
_start:
{
uint8_t v___x_50423__boxed_1177_; lean_object* v_res_1178_; 
v___x_50423__boxed_1177_ = lean_unbox(v___x_1160_);
v_res_1178_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(v___x_1157_, v___x_1158_, v_stx_1159_, v___x_50423__boxed_1177_, v___x_1161_, v___x_1162_, v___x_1163_, v___x_1164_, v___x_1165_, v___x_1166_, v_only_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v_only_1167_);
lean_dec_ref(v___x_1157_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_bs_1181_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_bs_1181_);
return v___x_1183_;
}
else
{
lean_object* v_v_1184_; lean_object* v___x_1185_; lean_object* v_bs_x27_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_v_1184_ = lean_array_uget(v_bs_1181_, v_i_1180_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v_bs_x27_1186_ = lean_array_uset(v_bs_1181_, v_i_1180_, v___x_1185_);
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1180_, v___x_1187_);
v___x_1189_ = lean_array_uset(v_bs_x27_1186_, v_i_1180_, v_v_1184_);
v_i_1180_ = v___x_1188_;
v_bs_1181_ = v___x_1189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_bs_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1194_, v_i_boxed_1195_, v_bs_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0));
v___x_1217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1));
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3));
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
lean_inc(v_stx_1206_);
v___x_1221_ = l_Lean_Syntax_isOfKind(v_stx_1206_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v_stx_1206_);
v___x_1222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = l_Lean_Syntax_getArg(v_stx_1206_, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_getArgs(v___x_1224_);
lean_dec(v___x_1224_);
v_sz_1226_ = lean_array_size(v___x_1225_);
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1226_, v___x_1227_, v___x_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_dec(v_stx_1206_);
v___x_1229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1279_; 
v_val_1230_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1232_ = v___x_1228_;
v_isShared_1233_ = v_isSharedCheck_1279_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_val_1230_);
lean_dec(v___x_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1279_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v_only_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1234_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_unsigned_to_nat(2u);
v___x_1270_ = l_Lean_Syntax_getArg(v_stx_1206_, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_isNone(v___x_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; 
lean_inc(v___x_1270_);
v___x_1272_ = l_Lean_Syntax_matchesNull(v___x_1270_, v___x_1223_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec(v___x_1270_);
lean_del_object(v___x_1232_);
lean_dec(v_val_1230_);
lean_dec(v_stx_1206_);
v___x_1273_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1273_;
}
else
{
lean_object* v_only_1274_; lean_object* v___x_1276_; 
v_only_1274_ = l_Lean_Syntax_getArg(v___x_1270_, v___x_1235_);
lean_dec(v___x_1270_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v_only_1274_);
v___x_1276_ = v___x_1232_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_only_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v_only_1252_ = v___x_1276_;
v___y_1253_ = v_a_1207_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
goto v___jp_1251_;
}
}
}
else
{
lean_object* v___x_1278_; 
lean_dec(v___x_1270_);
lean_del_object(v___x_1232_);
v___x_1278_ = lean_box(0);
v_only_1252_ = v___x_1278_;
v___y_1253_ = v_a_1207_;
v___y_1254_ = v_a_1208_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
goto v___jp_1251_;
}
v___jp_1236_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; 
v___x_1247_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1246_);
lean_dec_ref(v___y_1246_);
v___x_1248_ = lean_box(v___x_1221_);
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1249_, 0, v___x_1247_);
lean_closure_set(v___f_1249_, 1, v___x_1223_);
lean_closure_set(v___f_1249_, 2, v_stx_1206_);
lean_closure_set(v___f_1249_, 3, v___x_1248_);
lean_closure_set(v___f_1249_, 4, v___x_1234_);
lean_closure_set(v___f_1249_, 5, v___x_1235_);
lean_closure_set(v___f_1249_, 6, v___x_1216_);
lean_closure_set(v___f_1249_, 7, v___x_1217_);
lean_closure_set(v___f_1249_, 8, v___x_1218_);
lean_closure_set(v___f_1249_, 9, v___x_1219_);
lean_closure_set(v___f_1249_, 10, v___y_1237_);
v___x_1250_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_1230_, v___f_1249_, v___y_1239_, v___y_1240_, v___y_1244_, v___y_1238_, v___y_1242_, v___y_1245_, v___y_1241_, v___y_1243_);
return v___x_1250_;
}
v___jp_1251_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = lean_unsigned_to_nat(3u);
v___x_1262_ = l_Lean_Syntax_getArg(v_stx_1206_, v___x_1261_);
v___x_1263_ = l_Lean_Syntax_isNone(v___x_1262_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
lean_inc(v___x_1262_);
v___x_1264_ = l_Lean_Syntax_matchesNull(v___x_1262_, v___x_1261_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v___x_1262_);
lean_dec(v_only_1252_);
lean_dec(v_val_1230_);
lean_dec(v_stx_1206_);
v___x_1265_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v_params_x3f_1267_; 
v___x_1266_ = l_Lean_Syntax_getArg(v___x_1262_, v___x_1223_);
lean_dec(v___x_1262_);
v_params_x3f_1267_ = l_Lean_Syntax_getArgs(v___x_1266_);
lean_dec(v___x_1266_);
v___y_1237_ = v_only_1252_;
v___y_1238_ = v___y_1256_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1259_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1255_;
v___y_1245_ = v___y_1258_;
v___y_1246_ = v_params_x3f_1267_;
goto v___jp_1236_;
}
}
else
{
lean_object* v___x_1268_; 
lean_dec(v___x_1262_);
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___y_1237_ = v_only_1252_;
v___y_1238_ = v___y_1256_;
v___y_1239_ = v___y_1253_;
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1259_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1255_;
v___y_1245_ = v___y_1258_;
v___y_1246_ = v___x_1268_;
goto v___jp_1236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object* v_00_u03b1_1291_, lean_object* v_msg_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_1292_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(v_00_u03b1_1304_, v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object* v_ref_1317_, lean_object* v_msgData_1318_, uint8_t v_severity_1319_, uint8_t v_isSilent_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_1317_, v_msgData_1318_, v_severity_1319_, v_isSilent_1320_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1332_, lean_object* v_msgData_1333_, lean_object* v_severity_1334_, lean_object* v_isSilent_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_severity_boxed_1346_; uint8_t v_isSilent_boxed_1347_; lean_object* v_res_1348_; 
v_severity_boxed_1346_ = lean_unbox(v_severity_1334_);
v_isSilent_boxed_1347_ = lean_unbox(v_isSilent_1335_);
v_res_1348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(v_ref_1332_, v_msgData_1333_, v_severity_boxed_1346_, v_isSilent_boxed_1347_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v_ref_1332_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1389_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_1391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14));
v___x_1392_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_1393_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1389_, v___x_1390_, v___x_1391_, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_1395_;
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
