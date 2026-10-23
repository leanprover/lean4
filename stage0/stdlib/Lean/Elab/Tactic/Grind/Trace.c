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
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_symSimpMethods_20_; lean_object* v_symDSimpMethods_21_; lean_object* v_anchorRefs_x3f_22_; uint8_t v_cheapCases_23_; uint8_t v_reportMVarIssue_24_; lean_object* v_splitSource_25_; lean_object* v_ematchDiagSource_26_; lean_object* v_symPrios_27_; lean_object* v_extensions_28_; uint8_t v_debug_29_; uint8_t v_ematchDiag_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_genLocal_38_; lean_object* v_instances_39_; uint8_t v_matchEqs_40_; uint8_t v_splitMatch_41_; uint8_t v_splitIte_42_; uint8_t v_splitIndPred_43_; uint8_t v_splitImp_44_; lean_object* v_canonHeartbeats_45_; uint8_t v_ext_46_; uint8_t v_extAll_47_; uint8_t v_etaStruct_48_; uint8_t v_funext_49_; uint8_t v_lookahead_50_; uint8_t v_verbose_51_; uint8_t v_clean_52_; uint8_t v_qlia_53_; uint8_t v_mbtc_54_; uint8_t v_zetaDelta_55_; uint8_t v_zeta_56_; uint8_t v_distrib_57_; lean_object* v_maxChar_58_; uint8_t v_ring_59_; lean_object* v_ringSteps_60_; lean_object* v_ringMaxDegree_61_; uint8_t v_linarith_62_; uint8_t v_lia_63_; lean_object* v_liaSteps_64_; lean_object* v_liaReorders_65_; lean_object* v_liaReorderCases_66_; uint8_t v_hom_67_; uint8_t v_ac_68_; lean_object* v_acSteps_69_; lean_object* v_exp_70_; uint8_t v_abstractProof_71_; uint8_t v_inj_72_; uint8_t v_order_73_; lean_object* v_min_74_; lean_object* v_detailed_75_; uint8_t v_useSorry_76_; uint8_t v_revert_77_; uint8_t v_funCC_78_; uint8_t v_reducible_79_; lean_object* v_maxSuggestions_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
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
v_markInstances_31_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 1);
v_lax_32_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 2);
v_suggestions_33_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 3);
v_locals_34_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 4);
v_splits_35_ = lean_ctor_get(v_config_12_, 0);
v_ematch_36_ = lean_ctor_get(v_config_12_, 1);
v_gen_37_ = lean_ctor_get(v_config_12_, 2);
v_genLocal_38_ = lean_ctor_get(v_config_12_, 3);
v_instances_39_ = lean_ctor_get(v_config_12_, 4);
v_matchEqs_40_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 5);
v_splitMatch_41_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 6);
v_splitIte_42_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 7);
v_splitIndPred_43_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 8);
v_splitImp_44_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 9);
v_canonHeartbeats_45_ = lean_ctor_get(v_config_12_, 5);
v_ext_46_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 10);
v_extAll_47_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 11);
v_etaStruct_48_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 12);
v_funext_49_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 13);
v_lookahead_50_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 14);
v_verbose_51_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 15);
v_clean_52_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 16);
v_qlia_53_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 17);
v_mbtc_54_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 18);
v_zetaDelta_55_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 19);
v_zeta_56_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 20);
v_distrib_57_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 21);
v_maxChar_58_ = lean_ctor_get(v_config_12_, 6);
v_ring_59_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 22);
v_ringSteps_60_ = lean_ctor_get(v_config_12_, 7);
v_ringMaxDegree_61_ = lean_ctor_get(v_config_12_, 8);
v_linarith_62_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 23);
v_lia_63_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 24);
v_liaSteps_64_ = lean_ctor_get(v_config_12_, 9);
v_liaReorders_65_ = lean_ctor_get(v_config_12_, 10);
v_liaReorderCases_66_ = lean_ctor_get(v_config_12_, 11);
v_hom_67_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 25);
v_ac_68_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 26);
v_acSteps_69_ = lean_ctor_get(v_config_12_, 12);
v_exp_70_ = lean_ctor_get(v_config_12_, 13);
v_abstractProof_71_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 27);
v_inj_72_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 28);
v_order_73_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 29);
v_min_74_ = lean_ctor_get(v_config_12_, 14);
v_detailed_75_ = lean_ctor_get(v_config_12_, 15);
v_useSorry_76_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 30);
v_revert_77_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 31);
v_funCC_78_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 32);
v_reducible_79_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*17 + 33);
v_maxSuggestions_80_ = lean_ctor_get(v_config_12_, 16);
v___x_81_ = 1;
lean_inc(v_maxSuggestions_80_);
lean_inc(v_detailed_75_);
lean_inc(v_min_74_);
lean_inc(v_exp_70_);
lean_inc(v_acSteps_69_);
lean_inc(v_liaReorderCases_66_);
lean_inc(v_liaReorders_65_);
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
v___x_82_ = lean_alloc_ctor(0, 17, 34);
lean_ctor_set(v___x_82_, 0, v_splits_35_);
lean_ctor_set(v___x_82_, 1, v_ematch_36_);
lean_ctor_set(v___x_82_, 2, v_gen_37_);
lean_ctor_set(v___x_82_, 3, v_genLocal_38_);
lean_ctor_set(v___x_82_, 4, v_instances_39_);
lean_ctor_set(v___x_82_, 5, v_canonHeartbeats_45_);
lean_ctor_set(v___x_82_, 6, v_maxChar_58_);
lean_ctor_set(v___x_82_, 7, v_ringSteps_60_);
lean_ctor_set(v___x_82_, 8, v_ringMaxDegree_61_);
lean_ctor_set(v___x_82_, 9, v_liaSteps_64_);
lean_ctor_set(v___x_82_, 10, v_liaReorders_65_);
lean_ctor_set(v___x_82_, 11, v_liaReorderCases_66_);
lean_ctor_set(v___x_82_, 12, v_acSteps_69_);
lean_ctor_set(v___x_82_, 13, v_exp_70_);
lean_ctor_set(v___x_82_, 14, v_min_74_);
lean_ctor_set(v___x_82_, 15, v_detailed_75_);
lean_ctor_set(v___x_82_, 16, v_maxSuggestions_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 1, v_markInstances_31_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 2, v_lax_32_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 3, v_suggestions_33_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 4, v_locals_34_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 5, v_matchEqs_40_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 6, v_splitMatch_41_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 7, v_splitIte_42_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 8, v_splitIndPred_43_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 9, v_splitImp_44_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 10, v_ext_46_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 11, v_extAll_47_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 12, v_etaStruct_48_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 13, v_funext_49_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 14, v_lookahead_50_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 15, v_verbose_51_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 16, v_clean_52_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 17, v_qlia_53_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 18, v_mbtc_54_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 19, v_zetaDelta_55_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 20, v_zeta_56_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 21, v_distrib_57_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 22, v_ring_59_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 23, v_linarith_62_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 24, v_lia_63_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 25, v_hom_67_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 26, v_ac_68_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 27, v_abstractProof_71_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 28, v_inj_72_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 29, v_order_73_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 30, v_useSorry_76_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 31, v_revert_77_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 32, v_funCC_78_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*17 + 33, v_reducible_79_);
lean_inc_ref(v_extensions_28_);
lean_inc_ref(v_symPrios_27_);
lean_inc(v_ematchDiagSource_26_);
lean_inc(v_splitSource_25_);
lean_inc(v_anchorRefs_x3f_22_);
lean_inc_ref(v_symDSimpMethods_21_);
lean_inc_ref(v_symSimpMethods_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_83_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_83_, 0, v_simp_18_);
lean_ctor_set(v___x_83_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_83_, 2, v_symSimpMethods_20_);
lean_ctor_set(v___x_83_, 3, v_symDSimpMethods_21_);
lean_ctor_set(v___x_83_, 4, v___x_82_);
lean_ctor_set(v___x_83_, 5, v_anchorRefs_x3f_22_);
lean_ctor_set(v___x_83_, 6, v_splitSource_25_);
lean_ctor_set(v___x_83_, 7, v_ematchDiagSource_26_);
lean_ctor_set(v___x_83_, 8, v_symPrios_27_);
lean_ctor_set(v___x_83_, 9, v_extensions_28_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*10, v_cheapCases_23_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*10 + 1, v_reportMVarIssue_24_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*10 + 2, v_debug_29_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*10 + 3, v_ematchDiag_30_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_84_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_84_, 0, v_toContext_13_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
lean_ctor_set(v___x_84_, 2, v_sctx_14_);
lean_ctor_set(v___x_84_, 3, v_methods_15_);
lean_ctor_set(v___x_84_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_85_ = lean_apply_9(v_x_1_, v___x_84_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_97_, lean_object* v_x_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_109_, lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_109_, v_x_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
lean_object* v_name_123_; lean_object* v_defValue_124_; lean_object* v_map_125_; lean_object* v___x_126_; 
v_name_123_ = lean_ctor_get(v_opt_122_, 0);
v_defValue_124_ = lean_ctor_get(v_opt_122_, 1);
v_map_125_ = lean_ctor_get(v_opts_121_, 0);
v___x_126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_125_, v_name_123_);
if (lean_obj_tag(v___x_126_) == 0)
{
uint8_t v___x_127_; 
v___x_127_ = lean_unbox(v_defValue_124_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; 
v_val_128_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_126_, 1);
if (lean_obj_tag(v_val_128_) == 1)
{
uint8_t v_v_129_; 
v_v_129_ = lean_ctor_get_uint8(v_val_128_, 0);
lean_dec_ref_known(v_val_128_, 0);
return v_v_129_;
}
else
{
uint8_t v___x_130_; 
lean_dec(v_val_128_);
v___x_130_ = lean_unbox(v_defValue_124_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object* v_opts_131_, lean_object* v_opt_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v_opts_131_, v_opt_132_);
lean_dec_ref(v_opt_132_);
lean_dec_ref(v_opts_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Array_mkArray0___redArg();
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object* v_goal_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_seq_173_; lean_object* v_goal_174_; lean_object* v_seq_177_; lean_object* v___y_179_; lean_object* v___y_180_; uint8_t v___y_181_; lean_object* v___y_182_; lean_object* v_mvarId_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v_seq_242_; lean_object* v_goal_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_seq_177_ = lean_box(0);
v___x_287_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_169_);
v___x_288_ = l_Lean_Meta_tactic_hygienic;
v___x_289_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_287_, v___x_288_);
lean_dec_ref(v___x_287_);
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7));
lean_inc_ref(v_goal_161_);
v___x_291_ = l_Lean_Meta_Grind_Goal_intros(v_goal_161_, v___x_290_, v___x_289_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_goal_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_goal_161_);
v_goal_293_ = lean_ctor_get(v_a_292_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_a_292_, 0);
lean_dec(v_unused_322_);
v___x_295_ = v_a_292_;
v_isShared_296_ = v_isSharedCheck_321_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_goal_293_);
lean_dec(v_a_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_321_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_293_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v_ref_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v_ref_299_ = lean_ctor_get(v_a_169_, 2);
v___x_300_ = 0;
v___x_301_ = l_Lean_SourceInfo_fromRef(v_ref_299_, v___x_300_);
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9));
v___x_303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10));
lean_inc(v___x_301_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 2);
lean_ctor_set(v___x_295_, 1, v___x_303_);
lean_ctor_set(v___x_295_, 0, v___x_301_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_312_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12));
v___x_307_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13);
lean_inc(v___x_301_);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_301_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = l_Lean_Syntax_node2(v___x_301_, v___x_302_, v___x_305_, v___x_308_);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_seq_177_);
v___x_311_ = l_List_appendTR___redArg(v_seq_177_, v___x_310_);
v_seq_242_ = v___x_311_;
v_goal_243_ = v_a_298_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
v___y_250_ = v_a_168_;
v___y_251_ = v_a_169_;
v___y_252_ = v_a_170_;
goto v___jp_241_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_del_object(v___x_295_);
v_a_313_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_297_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_297_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
else
{
lean_dec(v_a_292_);
v_seq_242_ = v_seq_177_;
v_goal_243_ = v_goal_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
v___y_249_ = v_a_167_;
v___y_250_ = v_a_168_;
v___y_251_ = v_a_169_;
v___y_252_ = v_a_170_;
goto v___jp_241_;
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v_goal_161_);
v_a_323_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_291_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_291_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_seq_173_);
lean_ctor_set(v___x_175_, 1, v_goal_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
v___jp_178_:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_MVarId_byContra_x3f(v_mvarId_183_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
if (lean_obj_tag(v_a_194_) == 1)
{
lean_object* v_val_195_; lean_object* v___x_196_; 
lean_dec_ref(v___y_179_);
v_val_195_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v_a_194_, 1);
v___x_196_ = l_Lean_Meta_intro1Core(v_val_195_, v___y_181_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v_snd_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_223_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v_snd_198_ = lean_ctor_get(v_a_197_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_a_197_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v_a_197_, 0);
lean_dec(v_unused_224_);
v___x_200_ = v_a_197_;
v_isShared_201_ = v_isSharedCheck_223_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_snd_198_);
lean_dec(v_a_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_223_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___y_182_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___y_182_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_snd_198_);
v___x_203_ = v_reuseFailAlloc_222_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Goal_internalizeAll(v___x_203_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v_ref_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v_ref_206_ = lean_ctor_get(v___y_191_, 2);
v___x_207_ = l_Lean_SourceInfo_fromRef(v_ref_206_, v___y_181_);
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5));
v___x_209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6));
lean_inc(v___x_207_);
v___x_210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = l_Lean_Syntax_node1(v___x_207_, v___x_208_, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_seq_177_);
v___x_213_ = l_List_appendTR___redArg(v___y_180_, v___x_212_);
v_seq_173_ = v___x_213_;
v_goal_174_ = v_a_205_;
goto v___jp_172_;
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v___y_180_);
v_a_214_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_204_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_204_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v___y_182_);
lean_dec(v___y_180_);
v_a_225_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_196_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_196_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_dec(v_a_194_);
lean_dec_ref(v___y_182_);
v_seq_173_ = v___y_180_;
v_goal_174_ = v___y_179_;
goto v___jp_172_;
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v___y_182_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
v_a_233_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_193_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_193_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
v___jp_241_:
{
lean_object* v_toGoalState_253_; lean_object* v_mvarId_254_; lean_object* v___x_255_; 
v_toGoalState_253_ = lean_ctor_get(v_goal_243_, 0);
v_mvarId_254_ = lean_ctor_get(v_goal_243_, 1);
lean_inc(v_mvarId_254_);
v___x_255_ = l_Lean_MVarId_getType(v_mvarId_254_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_n(v_a_256_, 2);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = l_Lean_Expr_isFalse(v_a_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_inc_ref(v_toGoalState_253_);
v___x_258_ = l_Lean_Meta_isProp(v_a_256_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; uint8_t v___x_260_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v___x_260_ = lean_unbox(v_a_259_);
lean_dec(v_a_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_inc(v_mvarId_254_);
v___x_261_ = l_Lean_MVarId_exfalso(v_mvarId_254_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___y_179_ = v_goal_243_;
v___y_180_ = v_seq_242_;
v___y_181_ = v___x_257_;
v___y_182_ = v_toGoalState_253_;
v_mvarId_183_ = v_a_262_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
v___y_190_ = v___y_250_;
v___y_191_ = v___y_251_;
v___y_192_ = v___y_252_;
goto v___jp_178_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_toGoalState_253_);
lean_dec_ref(v_goal_243_);
lean_dec(v_seq_242_);
v_a_263_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_261_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_inc(v_mvarId_254_);
v___y_179_ = v_goal_243_;
v___y_180_ = v_seq_242_;
v___y_181_ = v___x_257_;
v___y_182_ = v_toGoalState_253_;
v_mvarId_183_ = v_mvarId_254_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
v___y_189_ = v___y_249_;
v___y_190_ = v___y_250_;
v___y_191_ = v___y_251_;
v___y_192_ = v___y_252_;
goto v___jp_178_;
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_toGoalState_253_);
lean_dec_ref(v_goal_243_);
lean_dec(v_seq_242_);
v_a_271_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_258_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_258_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_dec(v_a_256_);
v_seq_173_ = v_seq_242_;
v_goal_174_ = v_goal_243_;
goto v___jp_172_;
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_goal_243_);
lean_dec(v_seq_242_);
v_a_279_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_255_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_255_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object* v_goal_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_goal_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
v___x_344_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object* v_msgData_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_env_380_; uint8_t v___x_381_; lean_object* v_env_382_; lean_object* v___x_383_; lean_object* v_toCold_384_; lean_object* v_mctx_385_; lean_object* v_lctx_386_; lean_object* v_options_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_379_ = lean_st_ref_get(v___y_377_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_380_);
lean_dec(v___x_379_);
v___x_381_ = 0;
v_env_382_ = l_Lean_Environment_setRecordingDeps(v_env_380_, v___x_381_);
v___x_383_ = lean_st_ref_get(v___y_375_);
v_toCold_384_ = lean_ctor_get(v___y_376_, 0);
v_mctx_385_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_mctx_385_);
lean_dec(v___x_383_);
v_lctx_386_ = lean_ctor_get(v___y_374_, 2);
v_options_387_ = lean_ctor_get(v_toCold_384_, 2);
lean_inc_ref(v_options_387_);
lean_inc_ref(v_lctx_386_);
v___x_388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_388_, 0, v_env_382_);
lean_ctor_set(v___x_388_, 1, v_mctx_385_);
lean_ctor_set(v___x_388_, 2, v_lctx_386_);
lean_ctor_set(v___x_388_, 3, v_options_387_);
v___x_389_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_msgData_373_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object* v_msgData_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msgData_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
v_ref_404_ = lean_ctor_get(v___y_401_, 2);
v___x_405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 1)
{
lean_object* v_pre_431_; 
v_pre_431_ = lean_ctor_get(v_x_430_, 0);
switch(lean_obj_tag(v_pre_431_))
{
case 1:
{
lean_object* v_pre_432_; 
v_pre_432_ = lean_ctor_get(v_pre_431_, 0);
switch(lean_obj_tag(v_pre_432_))
{
case 0:
{
lean_object* v_str_433_; lean_object* v_str_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_str_433_ = lean_ctor_get(v_x_430_, 1);
v_str_434_ = lean_ctor_get(v_pre_431_, 1);
v___x_435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_436_ = lean_string_dec_eq(v_str_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_438_ = lean_string_dec_eq(v_str_434_, v___x_437_);
if (v___x_438_ == 0)
{
return v___x_438_;
}
else
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_440_ = lean_string_dec_eq(v_str_433_, v___x_439_);
if (v___x_440_ == 0)
{
return v___x_440_;
}
else
{
return v_suppressElabErrors_429_;
}
}
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_442_ = lean_string_dec_eq(v_str_433_, v___x_441_);
if (v___x_442_ == 0)
{
return v___x_442_;
}
else
{
return v_suppressElabErrors_429_;
}
}
}
case 1:
{
lean_object* v_pre_443_; 
v_pre_443_ = lean_ctor_get(v_pre_432_, 0);
if (lean_obj_tag(v_pre_443_) == 0)
{
lean_object* v_str_444_; lean_object* v_str_445_; lean_object* v_str_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_str_444_ = lean_ctor_get(v_x_430_, 1);
v_str_445_ = lean_ctor_get(v_pre_431_, 1);
v_str_446_ = lean_ctor_get(v_pre_432_, 1);
v___x_447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_448_ = lean_string_dec_eq(v_str_446_, v___x_447_);
if (v___x_448_ == 0)
{
return v___x_448_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_450_ = lean_string_dec_eq(v_str_445_, v___x_449_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_452_ = lean_string_dec_eq(v_str_444_, v___x_451_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
return v_suppressElabErrors_429_;
}
}
}
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 0;
return v___x_453_;
}
}
default: 
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
}
}
case 0:
{
lean_object* v_str_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_str_455_ = lean_ctor_get(v_x_430_, 1);
v___x_456_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_457_ = lean_string_dec_eq(v_str_455_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
return v_suppressElabErrors_429_;
}
}
default: 
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
}
else
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_suppressElabErrors_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_suppressElabErrors_boxed_462_ = lean_unbox(v_suppressElabErrors_460_);
v_res_463_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_462_, v_x_461_);
lean_dec(v_x_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_466_, lean_object* v_msgData_467_, uint8_t v_severity_468_, uint8_t v_isSilent_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; uint8_t v___y_479_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_toCold_483_; lean_object* v___y_484_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; uint8_t v___y_518_; uint8_t v___y_519_; lean_object* v___y_520_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; uint8_t v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; uint8_t v___y_550_; uint8_t v___y_551_; uint8_t v___x_561_; uint8_t v___y_563_; uint8_t v___x_569_; 
v___x_561_ = 2;
v___x_569_ = l_Lean_instBEqMessageSeverity_beq(v_severity_468_, v___x_561_);
if (v___x_569_ == 0)
{
v___y_563_ = v___x_569_;
goto v___jp_562_;
}
else
{
uint8_t v___x_570_; 
lean_inc_ref(v_msgData_467_);
v___x_570_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_467_);
if (v___x_570_ == 0)
{
v___y_563_ = v___x_570_;
goto v___jp_562_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_msgData_467_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
v___jp_475_:
{
lean_object* v_currNamespace_485_; lean_object* v_openDecls_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_traceState_495_; lean_object* v_cache_496_; lean_object* v_recordedDeps_497_; lean_object* v_messages_498_; lean_object* v_infoState_499_; lean_object* v_snapshotTasks_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_511_; 
v_currNamespace_485_ = lean_ctor_get(v_toCold_483_, 4);
v_openDecls_486_ = lean_ctor_get(v_toCold_483_, 5);
lean_inc(v_openDecls_486_);
lean_inc(v_currNamespace_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_currNamespace_485_);
lean_ctor_set(v___x_487_, 1, v_openDecls_486_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___y_481_);
lean_inc_ref(v___y_477_);
lean_inc_ref(v___y_476_);
v___x_489_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_489_, 0, v___y_476_);
lean_ctor_set(v___x_489_, 1, v___y_478_);
lean_ctor_set(v___x_489_, 2, v___y_482_);
lean_ctor_set(v___x_489_, 3, v___y_477_);
lean_ctor_set(v___x_489_, 4, v___x_488_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5, v___y_480_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 1, v___y_479_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 2, v_isSilent_469_);
v___x_490_ = lean_st_ref_take(v___y_484_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_490_, 1);
v_ngen_493_ = lean_ctor_get(v___x_490_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_490_, 3);
v_traceState_495_ = lean_ctor_get(v___x_490_, 4);
v_cache_496_ = lean_ctor_get(v___x_490_, 5);
v_recordedDeps_497_ = lean_ctor_get(v___x_490_, 6);
v_messages_498_ = lean_ctor_get(v___x_490_, 7);
v_infoState_499_ = lean_ctor_get(v___x_490_, 8);
v_snapshotTasks_500_ = lean_ctor_get(v___x_490_, 9);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_511_ == 0)
{
v___x_502_ = v___x_490_;
v_isShared_503_ = v_isSharedCheck_511_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snapshotTasks_500_);
lean_inc(v_infoState_499_);
lean_inc(v_messages_498_);
lean_inc(v_recordedDeps_497_);
lean_inc(v_cache_496_);
lean_inc(v_traceState_495_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_511_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_box(0);
v___x_505_ = l_Lean_MessageLog_add(v___x_489_, v_messages_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 7, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_traceState_495_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v_cache_496_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_recordedDeps_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_infoState_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 9, v_snapshotTasks_500_);
v___x_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_st_ref_put(v___y_484_, v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_504_);
return v___x_509_;
}
}
}
v___jp_512_:
{
lean_object* v_fileName_521_; lean_object* v_fileMap_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_538_; 
v_fileName_521_ = lean_ctor_get(v___y_515_, 0);
v_fileMap_522_ = lean_ctor_get(v___y_515_, 1);
v___x_523_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_467_);
v___x_524_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v___x_523_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_538_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_538_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc_ref_n(v_fileMap_522_, 2);
v___x_529_ = l_Lean_FileMap_toPosition(v_fileMap_522_, v___y_516_);
lean_dec(v___y_516_);
v___x_530_ = l_Lean_FileMap_toPosition(v_fileMap_522_, v___y_520_);
lean_dec(v___y_520_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0));
if (v___y_518_ == 0)
{
lean_del_object(v___x_527_);
lean_dec_ref(v___y_513_);
v___y_476_ = v_fileName_521_;
v___y_477_ = v___x_532_;
v___y_478_ = v___x_529_;
v___y_479_ = v___y_517_;
v___y_480_ = v___y_519_;
v___y_481_ = v_a_525_;
v___y_482_ = v___x_531_;
v_toCold_483_ = v___y_514_;
v___y_484_ = v___y_473_;
goto v___jp_475_;
}
else
{
uint8_t v___x_533_; 
lean_inc(v_a_525_);
v___x_533_ = l_Lean_MessageData_hasTag(v___y_513_, v_a_525_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec_ref_known(v___x_531_, 1);
lean_dec_ref(v___x_529_);
lean_dec(v_a_525_);
v___x_534_ = lean_box(0);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_534_);
v___x_536_ = v___x_527_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_del_object(v___x_527_);
v___y_476_ = v_fileName_521_;
v___y_477_ = v___x_532_;
v___y_478_ = v___x_529_;
v___y_479_ = v___y_517_;
v___y_480_ = v___y_519_;
v___y_481_ = v_a_525_;
v___y_482_ = v___x_531_;
v_toCold_483_ = v___y_514_;
v___y_484_ = v___y_473_;
goto v___jp_475_;
}
}
}
}
v___jp_539_:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Syntax_getTailPos_x3f(v___y_545_, v___y_544_);
lean_dec(v___y_545_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_inc(v___y_546_);
v___y_513_ = v___y_540_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_541_;
v___y_516_ = v___y_546_;
v___y_517_ = v___y_543_;
v___y_518_ = v___y_542_;
v___y_519_ = v___y_544_;
v___y_520_ = v___y_546_;
goto v___jp_512_;
}
else
{
lean_object* v_val_548_; 
v_val_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v___x_547_, 1);
v___y_513_ = v___y_540_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_541_;
v___y_516_ = v___y_546_;
v___y_517_ = v___y_543_;
v___y_518_ = v___y_542_;
v___y_519_ = v___y_544_;
v___y_520_ = v_val_548_;
goto v___jp_512_;
}
}
v___jp_549_:
{
lean_object* v_toCold_552_; lean_object* v_ref_553_; uint8_t v_suppressElabErrors_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v_ref_557_; lean_object* v___x_558_; 
v_toCold_552_ = lean_ctor_get(v___y_472_, 0);
v_ref_553_ = lean_ctor_get(v___y_472_, 2);
v_suppressElabErrors_554_ = lean_ctor_get_uint8(v___y_472_, sizeof(void*)*3 + 2);
v___x_555_ = lean_box(v_suppressElabErrors_554_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_556_, 0, v___x_555_);
v_ref_557_ = l_Lean_replaceRef(v_ref_466_, v_ref_553_);
v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_550_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___y_540_ = v___f_556_;
v___y_541_ = v_toCold_552_;
v___y_542_ = v_suppressElabErrors_554_;
v___y_543_ = v___y_551_;
v___y_544_ = v___y_550_;
v___y_545_ = v_ref_557_;
v___y_546_ = v___x_559_;
goto v___jp_539_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_558_, 1);
v___y_540_ = v___f_556_;
v___y_541_ = v_toCold_552_;
v___y_542_ = v_suppressElabErrors_554_;
v___y_543_ = v___y_551_;
v___y_544_ = v___y_550_;
v___y_545_ = v_ref_557_;
v___y_546_ = v_val_560_;
goto v___jp_539_;
}
}
v___jp_562_:
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = 1;
v___x_565_ = l_Lean_instBEqMessageSeverity_beq(v_severity_468_, v___x_564_);
if (v___x_565_ == 0)
{
v___y_550_ = v___y_563_;
v___y_551_ = v_severity_468_;
goto v___jp_549_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_472_);
v___x_567_ = l_Lean_warningAsError;
v___x_568_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_566_, v___x_567_);
lean_dec_ref(v___x_566_);
if (v___x_568_ == 0)
{
v___y_550_ = v___y_563_;
v___y_551_ = v_severity_468_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___y_563_;
v___y_551_ = v___x_561_;
goto v___jp_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_573_, lean_object* v_msgData_574_, lean_object* v_severity_575_, lean_object* v_isSilent_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v_severity_boxed_582_; uint8_t v_isSilent_boxed_583_; lean_object* v_res_584_; 
v_severity_boxed_582_ = lean_unbox(v_severity_575_);
v_isSilent_boxed_583_ = lean_unbox(v_isSilent_576_);
v_res_584_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_573_, v_msgData_574_, v_severity_boxed_582_, v_isSilent_boxed_583_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v_ref_573_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_585_, uint8_t v_severity_586_, uint8_t v_isSilent_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_ref_598_; lean_object* v___x_599_; 
v_ref_598_ = lean_ctor_get(v___y_595_, 2);
v___x_599_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_598_, v_msgData_585_, v_severity_586_, v_isSilent_587_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_600_, lean_object* v_severity_601_, lean_object* v_isSilent_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v_severity_boxed_613_; uint8_t v_isSilent_boxed_614_; lean_object* v_res_615_; 
v_severity_boxed_613_ = lean_unbox(v_severity_601_);
v_isSilent_boxed_614_ = lean_unbox(v_isSilent_602_);
v_res_615_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_600_, v_severity_boxed_613_, v_isSilent_boxed_614_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_msgData_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
v___x_627_ = 1;
v___x_628_ = 0;
v___x_629_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_616_, v___x_627_, v___x_628_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_msgData_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_msgData_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v___x_660_, lean_object* v_stx_661_, uint8_t v___x_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_a_672_, lean_object* v_params_673_, lean_object* v_____x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_suggestions_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_908_; 
v_fst_736_ = lean_ctor_get(v_____x_674_, 0);
v_snd_737_ = lean_ctor_get(v_____x_674_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_____x_674_);
if (v_isSharedCheck_908_ == 0)
{
v___x_739_ = v_____x_674_;
v_isShared_740_ = v_isSharedCheck_908_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_____x_674_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_908_;
goto v_resetjp_738_;
}
v___jp_685_:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_array_get_size(v_suggestions_686_);
v___x_690_ = lean_nat_dec_eq(v___x_689_, v___x_660_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = lean_box(0);
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_693_ = 4;
v___x_694_ = l_Lean_MessageData_nil;
v___x_695_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_661_, v_suggestions_686_, v___x_691_, v___x_692_, v___x_691_, v___x_693_, v___x_694_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_704_);
v___x_697_ = v___x_695_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_dec(v___x_695_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_box(v___x_662_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_695_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_713_ = lean_array_get(v___x_663_, v_suggestions_686_, v___x_664_);
lean_dec_ref(v_suggestions_686_);
v___x_714_ = lean_box(0);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_716_ = 4;
v___x_717_ = l_Lean_MessageData_nil;
v___x_718_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_661_, v___x_713_, v___x_714_, v___x_715_, v___x_714_, v___x_716_, v___x_717_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_727_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_box(v___x_662_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_718_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_718_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
v_resetjp_738_:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Action_run(v_snd_737_, v_a_665_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
if (lean_obj_tag(v_a_742_) == 0)
{
lean_object* v_seq_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_850_; 
v_seq_743_ = lean_ctor_get(v_a_742_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_850_ == 0)
{
v___x_745_ = v_a_742_;
v_isShared_746_ = v_isSharedCheck_850_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_seq_743_);
lean_dec(v_a_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_850_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_List_appendTR___redArg(v_fst_736_, v_seq_743_);
lean_inc(v___x_747_);
v___x_748_ = l_Lean_Meta_Grind_mkFinishTactic(v___x_747_, v_a_666_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v_suggestions_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_suggestions_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_833_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
lean_inc_n(v___x_747_, 2);
v___x_750_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v___x_747_);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_664_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v_a_672_);
lean_inc_ref(v_a_667_);
lean_inc_ref(v___x_811_);
v___x_833_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_811_, v_a_667_, v___x_747_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; uint8_t v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
if (v___x_835_ == 0)
{
v_suggestions_813_ = v___x_810_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
goto v___jp_812_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
lean_inc_ref(v___x_671_);
lean_inc_ref(v___x_670_);
lean_inc_ref(v___x_669_);
lean_inc_ref(v___x_668_);
v___x_837_ = l_Lean_Name_mkStr5(v___x_668_, v___x_669_, v___x_670_, v___x_671_, v___x_836_);
lean_inc(v___x_750_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_750_);
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
lean_ctor_set(v___x_840_, 3, v___x_839_);
lean_ctor_set(v___x_840_, 4, v___x_839_);
lean_ctor_set(v___x_840_, 5, v___x_839_);
v___x_841_ = lean_array_push(v___x_810_, v___x_840_);
v_suggestions_813_ = v___x_841_;
v___y_814_ = v___y_675_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
goto v___jp_812_;
}
}
else
{
lean_dec_ref_known(v___x_811_, 1);
lean_dec_ref(v___x_810_);
lean_dec(v___x_750_);
lean_dec(v_a_749_);
lean_dec(v___x_747_);
lean_del_object(v___x_745_);
lean_del_object(v___x_739_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
return v___x_833_;
}
v___jp_751_:
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_array_get_size(v_suggestions_752_);
v___x_763_ = lean_nat_dec_eq(v___x_762_, v___x_664_);
if (v___x_763_ == 0)
{
lean_dec(v___x_750_);
lean_dec(v___x_747_);
lean_del_object(v___x_745_);
lean_del_object(v___x_739_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
v_suggestions_686_ = v_suggestions_752_;
v___y_687_ = v___y_760_;
v___y_688_ = v___y_761_;
goto v___jp_685_;
}
else
{
lean_object* v___x_764_; 
lean_dec_ref(v_suggestions_752_);
v___x_764_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v___x_747_, v___y_760_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_mvarId_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_800_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_mvarId_766_ = lean_ctor_get(v_a_667_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_a_667_, 0);
lean_dec(v_unused_801_);
v___x_768_ = v_a_667_;
v_isShared_769_ = v_isSharedCheck_800_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_mvarId_766_);
lean_dec(v_a_667_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_800_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_770_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3);
v___x_771_ = l_Lean_MessageData_ofSyntax(v_a_765_);
v___x_772_ = l_Lean_indentD(v___x_771_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 7);
lean_ctor_set(v___x_768_, 1, v___x_772_);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_774_ = v___x_768_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_799_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 7);
lean_ctor_set(v___x_739_, 1, v___x_775_);
lean_ctor_set(v___x_739_, 0, v___x_774_);
v___x_777_ = v___x_739_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_798_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v_mvarId_766_);
v___x_779_ = v___x_745_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_mvarId_766_);
v___x_779_ = v_reuseFailAlloc_797_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v___x_780_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref_known(v___x_781_, 1);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
v___x_783_ = l_Lean_Name_mkStr5(v___x_668_, v___x_669_, v___x_670_, v___x_671_, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_750_);
v___x_785_ = lean_box(0);
v___x_786_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
lean_ctor_set(v___x_786_, 3, v___x_785_);
lean_ctor_set(v___x_786_, 4, v___x_785_);
lean_ctor_set(v___x_786_, 5, v___x_785_);
v___x_787_ = lean_mk_empty_array_with_capacity(v___x_660_);
v___x_788_ = lean_array_push(v___x_787_, v___x_786_);
v_suggestions_686_ = v___x_788_;
v___y_687_ = v___y_760_;
v___y_688_ = v___y_761_;
goto v___jp_685_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v___x_750_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_stx_661_);
v_a_789_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_781_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_781_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
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
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_750_);
lean_del_object(v___x_745_);
lean_del_object(v___x_739_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
v_a_802_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_764_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_764_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
v___jp_812_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_box(0);
lean_inc(v_a_749_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v_a_749_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
lean_inc_ref(v_a_667_);
v___x_825_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_811_, v_a_667_, v___x_824_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; uint8_t v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = lean_unbox(v_a_826_);
lean_dec(v_a_826_);
if (v___x_827_ == 0)
{
lean_dec(v_a_749_);
v_suggestions_752_ = v_suggestions_813_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
goto v___jp_751_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8));
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_a_749_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
lean_ctor_set(v___x_831_, 3, v___x_830_);
lean_ctor_set(v___x_831_, 4, v___x_830_);
lean_ctor_set(v___x_831_, 5, v___x_830_);
v___x_832_ = lean_array_push(v_suggestions_813_, v___x_831_);
v_suggestions_752_ = v___x_832_;
v___y_753_ = v___y_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
goto v___jp_751_;
}
}
else
{
lean_dec_ref(v_suggestions_813_);
lean_dec(v___x_750_);
lean_dec(v_a_749_);
lean_dec(v___x_747_);
lean_del_object(v___x_745_);
lean_del_object(v___x_739_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
return v___x_825_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v___x_747_);
lean_del_object(v___x_745_);
lean_del_object(v___x_739_);
lean_dec_ref(v_a_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
v_a_842_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_748_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_748_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
else
{
lean_object* v_gs_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_899_; 
lean_del_object(v___x_739_);
lean_dec(v_fst_736_);
lean_dec_ref(v_a_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
v_gs_851_ = lean_ctor_get(v_a_742_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_899_ == 0)
{
v___x_853_ = v_a_742_;
v_isShared_854_ = v_isSharedCheck_899_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_gs_851_);
lean_dec(v_a_742_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_899_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
if (lean_obj_tag(v_gs_851_) == 1)
{
lean_object* v_head_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_895_; 
v_head_855_ = lean_ctor_get(v_gs_851_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_gs_851_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_gs_851_, 1);
lean_dec(v_unused_896_);
v___x_857_ = v_gs_851_;
v_isShared_858_ = v_isSharedCheck_895_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_head_855_);
lean_dec(v_gs_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_895_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_head_855_);
v___x_860_ = v___x_853_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_head_855_);
v___x_860_ = v_reuseFailAlloc_894_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Meta_Grind_mkResult(v_params_673_, v___x_860_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_862_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 7);
lean_ctor_set(v___x_857_, 1, v_a_864_);
lean_ctor_set(v___x_857_, 0, v___x_865_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_864_);
v___x_867_ = v_reuseFailAlloc_877_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v___x_868_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_867_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_857_);
v_a_878_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_863_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_863_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_del_object(v___x_857_);
v_a_886_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_861_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_861_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_853_);
lean_dec(v_gs_851_);
v___x_897_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12);
v___x_898_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_897_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_739_);
lean_dec(v_fst_736_);
lean_dec_ref(v_a_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_stx_661_);
v_a_900_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_741_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_741_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v___x_909_ = _args[0];
lean_object* v_stx_910_ = _args[1];
lean_object* v___x_911_ = _args[2];
lean_object* v___x_912_ = _args[3];
lean_object* v___x_913_ = _args[4];
lean_object* v_a_914_ = _args[5];
lean_object* v_a_915_ = _args[6];
lean_object* v_a_916_ = _args[7];
lean_object* v___x_917_ = _args[8];
lean_object* v___x_918_ = _args[9];
lean_object* v___x_919_ = _args[10];
lean_object* v___x_920_ = _args[11];
lean_object* v_a_921_ = _args[12];
lean_object* v_params_922_ = _args[13];
lean_object* v_____x_923_ = _args[14];
lean_object* v___y_924_ = _args[15];
lean_object* v___y_925_ = _args[16];
lean_object* v___y_926_ = _args[17];
lean_object* v___y_927_ = _args[18];
lean_object* v___y_928_ = _args[19];
lean_object* v___y_929_ = _args[20];
lean_object* v___y_930_ = _args[21];
lean_object* v___y_931_ = _args[22];
lean_object* v___y_932_ = _args[23];
lean_object* v___y_933_ = _args[24];
_start:
{
uint8_t v___x_49631__boxed_934_; lean_object* v_res_935_; 
v___x_49631__boxed_934_ = lean_unbox(v___x_911_);
v_res_935_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v___x_909_, v_stx_910_, v___x_49631__boxed_934_, v___x_912_, v___x_913_, v_a_914_, v_a_915_, v_a_916_, v___x_917_, v___x_918_, v___x_919_, v___x_920_, v_a_921_, v_params_922_, v_____x_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v_params_922_);
lean_dec_ref(v_a_915_);
lean_dec(v___x_913_);
lean_dec_ref(v___x_912_);
lean_dec(v___x_909_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t v_sym_936_, lean_object* v_a_937_, lean_object* v___f_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
if (v_sym_936_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_a_937_);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
v___x_951_ = lean_apply_11(v___f_938_, v___x_950_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, lean_box(0));
return v___x_951_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_a_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
v___x_954_ = lean_apply_11(v___f_938_, v_a_953_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, lean_box(0));
return v___x_954_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec_ref(v___f_938_);
v_a_955_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_952_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v_sym_963_, lean_object* v_a_964_, lean_object* v___f_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_sym_boxed_976_; lean_object* v_res_977_; 
v_sym_boxed_976_ = lean_unbox(v_sym_963_);
v_res_977_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v_sym_boxed_976_, v_a_964_, v___f_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___y_978_, v___y_979_, v___y_980_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1000_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint8_t v___x_993_; 
v___x_993_ = lean_unbox(v_a_989_);
lean_dec(v_a_989_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_del_object(v___x_991_);
v___x_998_ = lean_box(0);
v___x_999_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_998_, v___y_980_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_988_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_988_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_stx_1022_, uint8_t v___x_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_a_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 2);
v___x_1043_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1020_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1034_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_params_1047_; uint8_t v_sym_1048_; lean_object* v___x_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___y_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_params_1047_ = lean_ctor_get(v___y_1033_, 4);
v_sym_1048_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*5);
v___x_1049_ = lean_box(v___x_1023_);
lean_inc_ref(v_params_1047_);
v___f_1050_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 25, 14);
lean_closure_set(v___f_1050_, 0, v___x_1021_);
lean_closure_set(v___f_1050_, 1, v_stx_1022_);
lean_closure_set(v___f_1050_, 2, v___x_1049_);
lean_closure_set(v___f_1050_, 3, v___x_1024_);
lean_closure_set(v___f_1050_, 4, v___x_1025_);
lean_closure_set(v___f_1050_, 5, v_a_1044_);
lean_closure_set(v___f_1050_, 6, v_a_1026_);
lean_closure_set(v___f_1050_, 7, v_a_1027_);
lean_closure_set(v___f_1050_, 8, v___x_1028_);
lean_closure_set(v___f_1050_, 9, v___x_1029_);
lean_closure_set(v___f_1050_, 10, v___x_1030_);
lean_closure_set(v___f_1050_, 11, v___x_1031_);
lean_closure_set(v___f_1050_, 12, v_a_1032_);
lean_closure_set(v___f_1050_, 13, v_params_1047_);
v___x_1051_ = lean_box(v_sym_1048_);
v___y_1052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 13, 3);
lean_closure_set(v___y_1052_, 0, v___x_1051_);
lean_closure_set(v___y_1052_, 1, v_a_1046_);
lean_closure_set(v___y_1052_, 2, v___f_1050_);
v___f_1053_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1053_, 0, v___y_1052_);
v___x_1054_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1053_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec_ref(v___y_1033_);
return v___x_1054_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1044_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_a_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v___x_1025_);
lean_dec_ref(v___x_1024_);
lean_dec(v_stx_1022_);
lean_dec(v___x_1021_);
v_a_1055_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1045_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_a_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v___x_1025_);
lean_dec_ref(v___x_1024_);
lean_dec(v_stx_1022_);
lean_dec(v___x_1021_);
v_a_1063_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1065_ = v___x_1043_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1043_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1067_ = lean_io_error_to_string(v_a_1063_);
v___x_1068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
lean_inc(v_ref_1042_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_ref_1042_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1070_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___x_1075_ = _args[0];
lean_object* v___x_1076_ = _args[1];
lean_object* v_stx_1077_ = _args[2];
lean_object* v___x_1078_ = _args[3];
lean_object* v___x_1079_ = _args[4];
lean_object* v___x_1080_ = _args[5];
lean_object* v_a_1081_ = _args[6];
lean_object* v_a_1082_ = _args[7];
lean_object* v___x_1083_ = _args[8];
lean_object* v___x_1084_ = _args[9];
lean_object* v___x_1085_ = _args[10];
lean_object* v___x_1086_ = _args[11];
lean_object* v_a_1087_ = _args[12];
lean_object* v___y_1088_ = _args[13];
lean_object* v___y_1089_ = _args[14];
lean_object* v___y_1090_ = _args[15];
lean_object* v___y_1091_ = _args[16];
lean_object* v___y_1092_ = _args[17];
lean_object* v___y_1093_ = _args[18];
lean_object* v___y_1094_ = _args[19];
lean_object* v___y_1095_ = _args[20];
lean_object* v___y_1096_ = _args[21];
_start:
{
uint8_t v___x_50302__boxed_1097_; lean_object* v_res_1098_; 
v___x_50302__boxed_1097_ = lean_unbox(v___x_1078_);
v_res_1098_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___x_1075_, v___x_1076_, v_stx_1077_, v___x_50302__boxed_1097_, v___x_1079_, v___x_1080_, v_a_1081_, v_a_1082_, v___x_1083_, v___x_1084_, v___x_1085_, v___x_1086_, v_a_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v_stx_1102_, uint8_t v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_only_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v___x_1100_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0));
v___x_1125_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1124_, v___y_1111_, v___y_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v_params_1127_; uint8_t v___y_1129_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v_params_1127_ = lean_ctor_get(v___y_1111_, 4);
lean_inc_ref(v_params_1127_);
if (lean_obj_tag(v_only_1110_) == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = 0;
v___y_1129_ = v___x_1134_;
goto v___jp_1128_;
}
else
{
v___y_1129_ = v___x_1103_;
goto v___jp_1128_;
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_unsigned_to_nat(10000u);
v___x_1131_ = lean_box(v___x_1103_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 22, 13);
lean_closure_set(v___f_1132_, 0, v___x_1130_);
lean_closure_set(v___f_1132_, 1, v___x_1101_);
lean_closure_set(v___f_1132_, 2, v_stx_1102_);
lean_closure_set(v___f_1132_, 3, v___x_1131_);
lean_closure_set(v___f_1132_, 4, v___x_1104_);
lean_closure_set(v___f_1132_, 5, v___x_1105_);
lean_closure_set(v___f_1132_, 6, v_a_1121_);
lean_closure_set(v___f_1132_, 7, v_a_1123_);
lean_closure_set(v___f_1132_, 8, v___x_1106_);
lean_closure_set(v___f_1132_, 9, v___x_1107_);
lean_closure_set(v___f_1132_, 10, v___x_1108_);
lean_closure_set(v___f_1132_, 11, v___x_1109_);
lean_closure_set(v___f_1132_, 12, v_a_1126_);
v___x_1133_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_1127_, v___x_1100_, v___y_1129_, v___f_1132_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v___y_1111_);
return v___x_1133_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_a_1123_);
lean_dec(v_a_1121_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v_stx_1102_);
lean_dec(v___x_1101_);
v_a_1135_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1125_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1125_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1121_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v_stx_1102_);
lean_dec(v___x_1101_);
v_a_1143_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1122_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1122_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec(v___x_1105_);
lean_dec_ref(v___x_1104_);
lean_dec(v_stx_1102_);
lean_dec(v___x_1101_);
v_a_1151_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1120_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1120_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object** _args){
lean_object* v___x_1159_ = _args[0];
lean_object* v___x_1160_ = _args[1];
lean_object* v_stx_1161_ = _args[2];
lean_object* v___x_1162_ = _args[3];
lean_object* v___x_1163_ = _args[4];
lean_object* v___x_1164_ = _args[5];
lean_object* v___x_1165_ = _args[6];
lean_object* v___x_1166_ = _args[7];
lean_object* v___x_1167_ = _args[8];
lean_object* v___x_1168_ = _args[9];
lean_object* v_only_1169_ = _args[10];
lean_object* v___y_1170_ = _args[11];
lean_object* v___y_1171_ = _args[12];
lean_object* v___y_1172_ = _args[13];
lean_object* v___y_1173_ = _args[14];
lean_object* v___y_1174_ = _args[15];
lean_object* v___y_1175_ = _args[16];
lean_object* v___y_1176_ = _args[17];
lean_object* v___y_1177_ = _args[18];
lean_object* v___y_1178_ = _args[19];
_start:
{
uint8_t v___x_50427__boxed_1179_; lean_object* v_res_1180_; 
v___x_50427__boxed_1179_ = lean_unbox(v___x_1162_);
v_res_1180_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(v___x_1159_, v___x_1160_, v_stx_1161_, v___x_50427__boxed_1179_, v___x_1163_, v___x_1164_, v___x_1165_, v___x_1166_, v___x_1167_, v___x_1168_, v_only_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v_only_1169_);
lean_dec_ref(v___x_1159_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_1181_, size_t v_i_1182_, lean_object* v_bs_1183_){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_usize_dec_lt(v_i_1182_, v_sz_1181_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_bs_1183_);
return v___x_1185_;
}
else
{
lean_object* v_v_1186_; lean_object* v___x_1187_; lean_object* v_bs_x27_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v_v_1186_ = lean_array_uget(v_bs_1183_, v_i_1182_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v_bs_x27_1188_ = lean_array_uset(v_bs_1183_, v_i_1182_, v___x_1187_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_add(v_i_1182_, v___x_1189_);
v___x_1191_ = lean_array_uset(v_bs_x27_1188_, v_i_1182_, v_v_1186_);
v_i_1182_ = v___x_1190_;
v_bs_1183_ = v___x_1191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_1193_, lean_object* v_i_1194_, lean_object* v_bs_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1193_);
lean_dec(v_sz_1193_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1196_, v_i_boxed_1197_, v_bs_1195_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0));
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1));
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3));
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
lean_inc(v_stx_1208_);
v___x_1223_ = l_Lean_Syntax_isOfKind(v_stx_1208_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec(v_stx_1208_);
v___x_1224_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = l_Lean_Syntax_getArg(v_stx_1208_, v___x_1225_);
v___x_1227_ = l_Lean_Syntax_getArgs(v___x_1226_);
lean_dec(v___x_1226_);
v_sz_1228_ = lean_array_size(v___x_1227_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1228_, v___x_1229_, v___x_1227_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_stx_1208_);
v___x_1231_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1281_; 
v_val_1232_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1234_ = v___x_1230_;
v_isShared_1235_ = v_isSharedCheck_1281_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_val_1232_);
lean_dec(v___x_1230_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1281_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v_only_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1236_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_unsigned_to_nat(2u);
v___x_1272_ = l_Lean_Syntax_getArg(v_stx_1208_, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_isNone(v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; 
lean_inc(v___x_1272_);
v___x_1274_ = l_Lean_Syntax_matchesNull(v___x_1272_, v___x_1225_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v___x_1272_);
lean_del_object(v___x_1234_);
lean_dec(v_val_1232_);
lean_dec(v_stx_1208_);
v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1275_;
}
else
{
lean_object* v_only_1276_; lean_object* v___x_1278_; 
v_only_1276_ = l_Lean_Syntax_getArg(v___x_1272_, v___x_1237_);
lean_dec(v___x_1272_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_only_1276_);
v___x_1278_ = v___x_1234_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_only_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_only_1254_ = v___x_1278_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
v___y_1262_ = v_a_1216_;
goto v___jp_1253_;
}
}
}
else
{
lean_object* v___x_1280_; 
lean_dec(v___x_1272_);
lean_del_object(v___x_1234_);
v___x_1280_ = lean_box(0);
v_only_1254_ = v___x_1280_;
v___y_1255_ = v_a_1209_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
v___y_1262_ = v_a_1216_;
goto v___jp_1253_;
}
v___jp_1238_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; 
v___x_1249_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1248_);
lean_dec_ref(v___y_1248_);
v___x_1250_ = lean_box(v___x_1223_);
v___f_1251_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1251_, 0, v___x_1249_);
lean_closure_set(v___f_1251_, 1, v___x_1225_);
lean_closure_set(v___f_1251_, 2, v_stx_1208_);
lean_closure_set(v___f_1251_, 3, v___x_1250_);
lean_closure_set(v___f_1251_, 4, v___x_1236_);
lean_closure_set(v___f_1251_, 5, v___x_1237_);
lean_closure_set(v___f_1251_, 6, v___x_1218_);
lean_closure_set(v___f_1251_, 7, v___x_1219_);
lean_closure_set(v___f_1251_, 8, v___x_1220_);
lean_closure_set(v___f_1251_, 9, v___x_1221_);
lean_closure_set(v___f_1251_, 10, v___y_1239_);
v___x_1252_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_1232_, v___f_1251_, v___y_1247_, v___y_1244_, v___y_1242_, v___y_1245_, v___y_1246_, v___y_1240_, v___y_1241_, v___y_1243_);
return v___x_1252_;
}
v___jp_1253_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(3u);
v___x_1264_ = l_Lean_Syntax_getArg(v_stx_1208_, v___x_1263_);
v___x_1265_ = l_Lean_Syntax_isNone(v___x_1264_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
lean_inc(v___x_1264_);
v___x_1266_ = l_Lean_Syntax_matchesNull(v___x_1264_, v___x_1263_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v___x_1264_);
lean_dec(v_only_1254_);
lean_dec(v_val_1232_);
lean_dec(v_stx_1208_);
v___x_1267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v_params_x3f_1269_; 
v___x_1268_ = l_Lean_Syntax_getArg(v___x_1264_, v___x_1225_);
lean_dec(v___x_1264_);
v_params_x3f_1269_ = l_Lean_Syntax_getArgs(v___x_1268_);
lean_dec(v___x_1268_);
v___y_1239_ = v_only_1254_;
v___y_1240_ = v___y_1260_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1262_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1258_;
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1255_;
v___y_1248_ = v_params_x3f_1269_;
goto v___jp_1238_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec(v___x_1264_);
v___x_1270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___y_1239_ = v_only_1254_;
v___y_1240_ = v___y_1260_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1257_;
v___y_1243_ = v___y_1262_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1258_;
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1255_;
v___y_1248_ = v___x_1270_;
goto v___jp_1238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object* v_00_u03b1_1293_, lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_1294_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(v_00_u03b1_1306_, v_msg_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object* v_ref_1319_, lean_object* v_msgData_1320_, uint8_t v_severity_1321_, uint8_t v_isSilent_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_1319_, v_msgData_1320_, v_severity_1321_, v_isSilent_1322_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1334_, lean_object* v_msgData_1335_, lean_object* v_severity_1336_, lean_object* v_isSilent_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_severity_boxed_1348_; uint8_t v_isSilent_boxed_1349_; lean_object* v_res_1350_; 
v_severity_boxed_1348_ = lean_unbox(v_severity_1336_);
v_isSilent_boxed_1349_ = lean_unbox(v_isSilent_1337_);
v_res_1350_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(v_ref_1334_, v_msgData_1335_, v_severity_boxed_1348_, v_isSilent_boxed_1349_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v_ref_1334_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1391_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_1393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14));
v___x_1394_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_1395_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_1397_;
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
