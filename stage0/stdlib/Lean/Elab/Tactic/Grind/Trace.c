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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_symSimpMethods_20_; lean_object* v_symDSimpMethods_21_; lean_object* v_anchorRefs_x3f_22_; uint8_t v_cheapCases_23_; uint8_t v_reportMVarIssue_24_; lean_object* v_splitSource_25_; lean_object* v_ematchDiagSource_26_; lean_object* v_symPrios_27_; lean_object* v_extensions_28_; uint8_t v_debug_29_; uint8_t v_ematchDiag_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_genLocal_38_; lean_object* v_instances_39_; uint8_t v_matchEqs_40_; uint8_t v_splitMatch_41_; uint8_t v_splitIte_42_; uint8_t v_splitIndPred_43_; uint8_t v_splitImp_44_; lean_object* v_canonHeartbeats_45_; uint8_t v_ext_46_; uint8_t v_extAll_47_; uint8_t v_etaStruct_48_; uint8_t v_funext_49_; uint8_t v_lookahead_50_; uint8_t v_verbose_51_; uint8_t v_clean_52_; uint8_t v_qlia_53_; uint8_t v_mbtc_54_; uint8_t v_zetaDelta_55_; uint8_t v_zeta_56_; uint8_t v_ring_57_; lean_object* v_ringSteps_58_; lean_object* v_ringMaxDegree_59_; uint8_t v_linarith_60_; uint8_t v_lia_61_; lean_object* v_liaSteps_62_; uint8_t v_hom_63_; uint8_t v_ac_64_; lean_object* v_acSteps_65_; lean_object* v_exp_66_; uint8_t v_abstractProof_67_; uint8_t v_inj_68_; uint8_t v_order_69_; lean_object* v_min_70_; lean_object* v_detailed_71_; uint8_t v_useSorry_72_; uint8_t v_revert_73_; uint8_t v_funCC_74_; uint8_t v_reducible_75_; lean_object* v_maxSuggestions_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
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
v_ring_57_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 21);
v_ringSteps_58_ = lean_ctor_get(v_config_12_, 6);
v_ringMaxDegree_59_ = lean_ctor_get(v_config_12_, 7);
v_linarith_60_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 22);
v_lia_61_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 23);
v_liaSteps_62_ = lean_ctor_get(v_config_12_, 8);
v_hom_63_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 24);
v_ac_64_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 25);
v_acSteps_65_ = lean_ctor_get(v_config_12_, 9);
v_exp_66_ = lean_ctor_get(v_config_12_, 10);
v_abstractProof_67_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 26);
v_inj_68_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 27);
v_order_69_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 28);
v_min_70_ = lean_ctor_get(v_config_12_, 11);
v_detailed_71_ = lean_ctor_get(v_config_12_, 12);
v_useSorry_72_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 29);
v_revert_73_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 30);
v_funCC_74_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 31);
v_reducible_75_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*14 + 32);
v_maxSuggestions_76_ = lean_ctor_get(v_config_12_, 13);
v___x_77_ = 1;
lean_inc(v_maxSuggestions_76_);
lean_inc(v_detailed_71_);
lean_inc(v_min_70_);
lean_inc(v_exp_66_);
lean_inc(v_acSteps_65_);
lean_inc(v_liaSteps_62_);
lean_inc(v_ringMaxDegree_59_);
lean_inc(v_ringSteps_58_);
lean_inc(v_canonHeartbeats_45_);
lean_inc(v_instances_39_);
lean_inc(v_genLocal_38_);
lean_inc(v_gen_37_);
lean_inc(v_ematch_36_);
lean_inc(v_splits_35_);
v___x_78_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_78_, 0, v_splits_35_);
lean_ctor_set(v___x_78_, 1, v_ematch_36_);
lean_ctor_set(v___x_78_, 2, v_gen_37_);
lean_ctor_set(v___x_78_, 3, v_genLocal_38_);
lean_ctor_set(v___x_78_, 4, v_instances_39_);
lean_ctor_set(v___x_78_, 5, v_canonHeartbeats_45_);
lean_ctor_set(v___x_78_, 6, v_ringSteps_58_);
lean_ctor_set(v___x_78_, 7, v_ringMaxDegree_59_);
lean_ctor_set(v___x_78_, 8, v_liaSteps_62_);
lean_ctor_set(v___x_78_, 9, v_acSteps_65_);
lean_ctor_set(v___x_78_, 10, v_exp_66_);
lean_ctor_set(v___x_78_, 11, v_min_70_);
lean_ctor_set(v___x_78_, 12, v_detailed_71_);
lean_ctor_set(v___x_78_, 13, v_maxSuggestions_76_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14, v___x_77_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 1, v_markInstances_31_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 2, v_lax_32_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 3, v_suggestions_33_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 4, v_locals_34_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 5, v_matchEqs_40_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 6, v_splitMatch_41_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 7, v_splitIte_42_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 8, v_splitIndPred_43_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 9, v_splitImp_44_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 10, v_ext_46_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 11, v_extAll_47_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 12, v_etaStruct_48_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 13, v_funext_49_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 14, v_lookahead_50_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 15, v_verbose_51_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 16, v_clean_52_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 17, v_qlia_53_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 18, v_mbtc_54_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 19, v_zetaDelta_55_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 20, v_zeta_56_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 21, v_ring_57_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 22, v_linarith_60_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 23, v_lia_61_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 24, v_hom_63_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 25, v_ac_64_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 26, v_abstractProof_67_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 27, v_inj_68_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 28, v_order_69_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 29, v_useSorry_72_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 30, v_revert_73_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 31, v_funCC_74_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*14 + 32, v_reducible_75_);
lean_inc_ref(v_extensions_28_);
lean_inc_ref(v_symPrios_27_);
lean_inc(v_ematchDiagSource_26_);
lean_inc(v_splitSource_25_);
lean_inc(v_anchorRefs_x3f_22_);
lean_inc_ref(v_symDSimpMethods_21_);
lean_inc_ref(v_symSimpMethods_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_79_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_79_, 0, v_simp_18_);
lean_ctor_set(v___x_79_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_79_, 2, v_symSimpMethods_20_);
lean_ctor_set(v___x_79_, 3, v_symDSimpMethods_21_);
lean_ctor_set(v___x_79_, 4, v___x_78_);
lean_ctor_set(v___x_79_, 5, v_anchorRefs_x3f_22_);
lean_ctor_set(v___x_79_, 6, v_splitSource_25_);
lean_ctor_set(v___x_79_, 7, v_ematchDiagSource_26_);
lean_ctor_set(v___x_79_, 8, v_symPrios_27_);
lean_ctor_set(v___x_79_, 9, v_extensions_28_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*10, v_cheapCases_23_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*10 + 1, v_reportMVarIssue_24_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*10 + 2, v_debug_29_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*10 + 3, v_ematchDiag_30_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_80_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_80_, 0, v_toContext_13_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
lean_ctor_set(v___x_80_, 2, v_sctx_14_);
lean_ctor_set(v___x_80_, 3, v_methods_15_);
lean_ctor_set(v___x_80_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_81_ = lean_apply_9(v_x_1_, v___x_80_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_93_, lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_105_, lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_105_, v_x_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(lean_object* v_opts_117_, lean_object* v_opt_118_){
_start:
{
lean_object* v_name_119_; lean_object* v_defValue_120_; lean_object* v_map_121_; lean_object* v___x_122_; 
v_name_119_ = lean_ctor_get(v_opt_118_, 0);
v_defValue_120_ = lean_ctor_get(v_opt_118_, 1);
v_map_121_ = lean_ctor_get(v_opts_117_, 0);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_121_, v_name_119_);
if (lean_obj_tag(v___x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = lean_unbox(v_defValue_120_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; 
v_val_124_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v___x_122_, 1);
if (lean_obj_tag(v_val_124_) == 1)
{
uint8_t v_v_125_; 
v_v_125_ = lean_ctor_get_uint8(v_val_124_, 0);
lean_dec_ref_known(v_val_124_, 0);
return v_v_125_;
}
else
{
uint8_t v___x_126_; 
lean_dec(v_val_124_);
v___x_126_ = lean_unbox(v_defValue_120_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0___boxed(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v_opts_127_, v_opt_128_);
lean_dec_ref(v_opt_128_);
lean_dec_ref(v_opts_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Array_mkArray0___redArg();
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(lean_object* v_goal_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_seq_169_; lean_object* v_goal_170_; lean_object* v_seq_173_; lean_object* v___y_175_; uint8_t v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v_mvarId_179_; lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v_seq_238_; lean_object* v_goal_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_seq_173_ = lean_box(0);
v___x_283_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_165_);
v___x_284_ = l_Lean_Meta_tactic_hygienic;
v___x_285_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_283_, v___x_284_);
lean_dec_ref(v___x_283_);
v___x_286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__7));
lean_inc_ref(v_goal_157_);
v___x_287_ = l_Lean_Meta_Grind_Goal_intros(v_goal_157_, v___x_286_, v___x_285_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
if (lean_obj_tag(v_a_288_) == 1)
{
lean_object* v_goal_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_goal_157_);
v_goal_289_ = lean_ctor_get(v_a_288_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_a_288_, 0);
lean_dec(v_unused_318_);
v___x_291_ = v_a_288_;
v_isShared_292_ = v_isSharedCheck_317_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_goal_289_);
lean_dec(v_a_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_317_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_289_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_ref_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v_ref_295_ = lean_ctor_get(v_a_165_, 2);
v___x_296_ = 0;
v___x_297_ = l_Lean_SourceInfo_fromRef(v_ref_295_, v___x_296_);
v___x_298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__9));
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__10));
lean_inc(v___x_297_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 2);
lean_ctor_set(v___x_291_, 1, v___x_299_);
lean_ctor_set(v___x_291_, 0, v___x_297_);
v___x_301_ = v___x_291_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_308_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__12));
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__13);
lean_inc(v___x_297_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_297_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___x_305_ = l_Lean_Syntax_node2(v___x_297_, v___x_298_, v___x_301_, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_seq_173_);
v___x_307_ = l_List_appendTR___redArg(v_seq_173_, v___x_306_);
v_seq_238_ = v___x_307_;
v_goal_239_ = v_a_294_;
v___y_240_ = v_a_158_;
v___y_241_ = v_a_159_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
goto v___jp_237_;
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_del_object(v___x_291_);
v_a_309_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_293_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_293_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
else
{
lean_dec(v_a_288_);
v_seq_238_ = v_seq_173_;
v_goal_239_ = v_goal_157_;
v___y_240_ = v_a_158_;
v___y_241_ = v_a_159_;
v___y_242_ = v_a_160_;
v___y_243_ = v_a_161_;
v___y_244_ = v_a_162_;
v___y_245_ = v_a_163_;
v___y_246_ = v_a_164_;
v___y_247_ = v_a_165_;
v___y_248_ = v_a_166_;
goto v___jp_237_;
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_goal_157_);
v_a_319_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_287_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_287_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
v___jp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_seq_169_);
lean_ctor_set(v___x_171_, 1, v_goal_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
v___jp_174_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_MVarId_byContra_x3f(v_mvarId_179_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
if (lean_obj_tag(v_a_190_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; 
lean_dec_ref(v___y_178_);
v_val_191_ = lean_ctor_get(v_a_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v_a_190_, 1);
v___x_192_ = l_Lean_Meta_intro1Core(v_val_191_, v___y_176_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_snd_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_219_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v_snd_194_ = lean_ctor_get(v_a_193_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_a_193_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_a_193_, 0);
lean_dec(v_unused_220_);
v___x_196_ = v_a_193_;
v_isShared_197_ = v_isSharedCheck_219_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_snd_194_);
lean_dec(v_a_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_219_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___y_177_);
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___y_177_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_snd_194_);
v___x_199_ = v_reuseFailAlloc_218_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Goal_internalizeAll(v___x_199_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v_ref_202_ = lean_ctor_get(v___y_187_, 2);
v___x_203_ = l_Lean_SourceInfo_fromRef(v_ref_202_, v___y_176_);
v___x_204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__5));
v___x_205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__6));
lean_inc(v___x_203_);
v___x_206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = l_Lean_Syntax_node1(v___x_203_, v___x_204_, v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_seq_173_);
v___x_209_ = l_List_appendTR___redArg(v___y_175_, v___x_208_);
v_seq_169_ = v___x_209_;
v_goal_170_ = v_a_201_;
goto v___jp_168_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v___y_175_);
v_a_210_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_200_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_200_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v___y_177_);
lean_dec(v___y_175_);
v_a_221_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_192_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_192_);
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
else
{
lean_dec(v_a_190_);
lean_dec_ref(v___y_177_);
v_seq_169_ = v___y_175_;
v_goal_170_ = v___y_178_;
goto v___jp_168_;
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_175_);
v_a_229_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_189_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_189_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
v___jp_237_:
{
lean_object* v_toGoalState_249_; lean_object* v_mvarId_250_; lean_object* v___x_251_; 
v_toGoalState_249_ = lean_ctor_get(v_goal_239_, 0);
v_mvarId_250_ = lean_ctor_get(v_goal_239_, 1);
lean_inc(v_mvarId_250_);
v___x_251_ = l_Lean_MVarId_getType(v_mvarId_250_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; uint8_t v___x_253_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_n(v_a_252_, 2);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = l_Lean_Expr_isFalse(v_a_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_inc_ref(v_toGoalState_249_);
v___x_254_ = l_Lean_Meta_isProp(v_a_252_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; uint8_t v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = lean_unbox(v_a_255_);
lean_dec(v_a_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_inc(v_mvarId_250_);
v___x_257_ = l_Lean_MVarId_exfalso(v_mvarId_250_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___y_175_ = v_seq_238_;
v___y_176_ = v___x_253_;
v___y_177_ = v_toGoalState_249_;
v___y_178_ = v_goal_239_;
v_mvarId_179_ = v_a_258_;
v___y_180_ = v___y_240_;
v___y_181_ = v___y_241_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
goto v___jp_174_;
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v_toGoalState_249_);
lean_dec_ref(v_goal_239_);
lean_dec(v_seq_238_);
v_a_259_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_inc(v_mvarId_250_);
v___y_175_ = v_seq_238_;
v___y_176_ = v___x_253_;
v___y_177_ = v_toGoalState_249_;
v___y_178_ = v_goal_239_;
v_mvarId_179_ = v_mvarId_250_;
v___y_180_ = v___y_240_;
v___y_181_ = v___y_241_;
v___y_182_ = v___y_242_;
v___y_183_ = v___y_243_;
v___y_184_ = v___y_244_;
v___y_185_ = v___y_245_;
v___y_186_ = v___y_246_;
v___y_187_ = v___y_247_;
v___y_188_ = v___y_248_;
goto v___jp_174_;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_toGoalState_249_);
lean_dec_ref(v_goal_239_);
lean_dec(v_seq_238_);
v_a_267_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_254_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_254_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_dec(v_a_252_);
v_seq_169_ = v_seq_238_;
v_goal_170_ = v_goal_239_;
goto v___jp_168_;
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_goal_239_);
lean_dec(v_seq_238_);
v_a_275_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_251_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_251_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___boxed(lean_object* v_goal_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_goal_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
return v_res_338_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_box(0);
v___x_340_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; uint8_t v___x_377_; lean_object* v_env_378_; lean_object* v___x_379_; lean_object* v_toCold_380_; lean_object* v_mctx_381_; lean_object* v_lctx_382_; lean_object* v_options_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_375_ = lean_st_ref_get(v___y_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___x_377_ = 0;
v_env_378_ = l_Lean_Environment_setRecordingDeps(v_env_376_, v___x_377_);
v___x_379_ = lean_st_ref_get(v___y_371_);
v_toCold_380_ = lean_ctor_get(v___y_372_, 0);
v_mctx_381_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_mctx_381_);
lean_dec(v___x_379_);
v_lctx_382_ = lean_ctor_get(v___y_370_, 2);
v_options_383_ = lean_ctor_get(v_toCold_380_, 2);
lean_inc_ref(v_options_383_);
lean_inc_ref(v_lctx_382_);
v___x_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_384_, 0, v_env_378_);
lean_ctor_set(v___x_384_, 1, v_mctx_381_);
lean_ctor_set(v___x_384_, 2, v_lctx_382_);
lean_ctor_set(v___x_384_, 3, v_options_383_);
v___x_385_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_msgData_369_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4___boxed(lean_object* v_msgData_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msgData_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_ref_400_ = lean_ctor_get(v___y_397_, 2);
v___x_401_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
lean_inc(v_ref_400_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_400_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg___boxed(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_425_, uint8_t v___y_426_, lean_object* v_x_427_){
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
return v_suppressElabErrors_425_;
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
return v_suppressElabErrors_425_;
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
return v_suppressElabErrors_425_;
}
}
}
}
else
{
return v___y_426_;
}
}
default: 
{
return v___y_426_;
}
}
}
case 0:
{
lean_object* v_str_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_str_450_ = lean_ctor_get(v_x_427_, 1);
v___x_451_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_452_ = lean_string_dec_eq(v_str_450_, v___x_451_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
return v_suppressElabErrors_425_;
}
}
default: 
{
return v___y_426_;
}
}
}
else
{
return v___y_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_453_, lean_object* v___y_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_suppressElabErrors_boxed_456_; uint8_t v___y_48869__boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v_suppressElabErrors_boxed_456_ = lean_unbox(v_suppressElabErrors_453_);
v___y_48869__boxed_457_ = lean_unbox(v___y_454_);
v_res_458_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_456_, v___y_48869__boxed_457_, v_x_455_);
lean_dec(v_x_455_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_461_, lean_object* v_msgData_462_, uint8_t v_severity_463_, uint8_t v_isSilent_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; uint8_t v___y_477_; lean_object* v_toCold_478_; lean_object* v___y_479_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; uint8_t v___y_512_; uint8_t v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; uint8_t v___y_540_; lean_object* v___y_541_; uint8_t v___y_545_; uint8_t v___y_546_; uint8_t v___y_547_; uint8_t v___x_558_; uint8_t v___y_560_; uint8_t v___y_561_; uint8_t v___y_562_; uint8_t v___y_564_; uint8_t v___x_572_; 
v___x_558_ = 2;
v___x_572_ = l_Lean_instBEqMessageSeverity_beq(v_severity_463_, v___x_558_);
if (v___x_572_ == 0)
{
v___y_564_ = v___x_572_;
goto v___jp_563_;
}
else
{
uint8_t v___x_573_; 
lean_inc_ref(v_msgData_462_);
v___x_573_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_462_);
v___y_564_ = v___x_573_;
goto v___jp_563_;
}
v___jp_470_:
{
lean_object* v_currNamespace_480_; lean_object* v_openDecls_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v_nextMacroScope_487_; lean_object* v_ngen_488_; lean_object* v_auxDeclNGen_489_; lean_object* v_traceState_490_; lean_object* v_cache_491_; lean_object* v_recordedDeps_492_; lean_object* v_messages_493_; lean_object* v_infoState_494_; lean_object* v_snapshotTasks_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_506_; 
v_currNamespace_480_ = lean_ctor_get(v_toCold_478_, 4);
v_openDecls_481_ = lean_ctor_get(v_toCold_478_, 5);
lean_inc(v_openDecls_481_);
lean_inc(v_currNamespace_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_currNamespace_480_);
lean_ctor_set(v___x_482_, 1, v_openDecls_481_);
v___x_483_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc_ref(v___y_476_);
v___x_484_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_484_, 0, v___y_476_);
lean_ctor_set(v___x_484_, 1, v___y_471_);
lean_ctor_set(v___x_484_, 2, v___y_475_);
lean_ctor_set(v___x_484_, 3, v___y_472_);
lean_ctor_set(v___x_484_, 4, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5, v___y_477_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5 + 1, v___y_474_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*5 + 2, v_isSilent_464_);
v___x_485_ = lean_st_ref_take(v___y_479_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
v_nextMacroScope_487_ = lean_ctor_get(v___x_485_, 1);
v_ngen_488_ = lean_ctor_get(v___x_485_, 2);
v_auxDeclNGen_489_ = lean_ctor_get(v___x_485_, 3);
v_traceState_490_ = lean_ctor_get(v___x_485_, 4);
v_cache_491_ = lean_ctor_get(v___x_485_, 5);
v_recordedDeps_492_ = lean_ctor_get(v___x_485_, 6);
v_messages_493_ = lean_ctor_get(v___x_485_, 7);
v_infoState_494_ = lean_ctor_get(v___x_485_, 8);
v_snapshotTasks_495_ = lean_ctor_get(v___x_485_, 9);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_506_ == 0)
{
v___x_497_ = v___x_485_;
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snapshotTasks_495_);
lean_inc(v_infoState_494_);
lean_inc(v_messages_493_);
lean_inc(v_recordedDeps_492_);
lean_inc(v_cache_491_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_489_);
lean_inc(v_ngen_488_);
lean_inc(v_nextMacroScope_487_);
lean_inc(v_env_486_);
lean_dec(v___x_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_MessageLog_add(v___x_484_, v_messages_493_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 7, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_env_486_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_nextMacroScope_487_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_ngen_488_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_auxDeclNGen_489_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_traceState_490_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_cache_491_);
lean_ctor_set(v_reuseFailAlloc_505_, 6, v_recordedDeps_492_);
lean_ctor_set(v_reuseFailAlloc_505_, 7, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_505_, 8, v_infoState_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 9, v_snapshotTasks_495_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_st_ref_put(v___y_479_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_499_);
return v___x_504_;
}
}
}
v___jp_507_:
{
lean_object* v_fileName_516_; lean_object* v_fileMap_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_533_; 
v_fileName_516_ = lean_ctor_get(v___y_510_, 0);
v_fileMap_517_ = lean_ctor_get(v___y_510_, 1);
v___x_518_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_462_);
v___x_519_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3_spec__4(v___x_518_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_533_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_533_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_533_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc_ref_n(v_fileMap_517_, 2);
v___x_524_ = l_Lean_FileMap_toPosition(v_fileMap_517_, v___y_514_);
lean_dec(v___y_514_);
v___x_525_ = l_Lean_FileMap_toPosition(v_fileMap_517_, v___y_515_);
lean_dec(v___y_515_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___closed__0));
if (v___y_513_ == 0)
{
lean_del_object(v___x_522_);
lean_dec_ref(v___y_509_);
v___y_471_ = v___x_524_;
v___y_472_ = v___x_527_;
v___y_473_ = v_a_520_;
v___y_474_ = v___y_511_;
v___y_475_ = v___x_526_;
v___y_476_ = v_fileName_516_;
v___y_477_ = v___y_512_;
v_toCold_478_ = v___y_508_;
v___y_479_ = v___y_468_;
goto v___jp_470_;
}
else
{
uint8_t v___x_528_; 
lean_inc(v_a_520_);
v___x_528_ = l_Lean_MessageData_hasTag(v___y_509_, v_a_520_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec_ref_known(v___x_526_, 1);
lean_dec_ref(v___x_524_);
lean_dec(v_a_520_);
v___x_529_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_529_);
v___x_531_ = v___x_522_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_del_object(v___x_522_);
v___y_471_ = v___x_524_;
v___y_472_ = v___x_527_;
v___y_473_ = v_a_520_;
v___y_474_ = v___y_511_;
v___y_475_ = v___x_526_;
v___y_476_ = v_fileName_516_;
v___y_477_ = v___y_512_;
v_toCold_478_ = v___y_508_;
v___y_479_ = v___y_468_;
goto v___jp_470_;
}
}
}
}
v___jp_534_:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Syntax_getTailPos_x3f(v___y_538_, v___y_540_);
lean_dec(v___y_538_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_inc(v___y_541_);
v___y_508_ = v___y_535_;
v___y_509_ = v___y_536_;
v___y_510_ = v___y_535_;
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_541_;
v___y_515_ = v___y_541_;
goto v___jp_507_;
}
else
{
lean_object* v_val_543_; 
v_val_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_542_, 1);
v___y_508_ = v___y_535_;
v___y_509_ = v___y_536_;
v___y_510_ = v___y_535_;
v___y_511_ = v___y_539_;
v___y_512_ = v___y_540_;
v___y_513_ = v___y_537_;
v___y_514_ = v___y_541_;
v___y_515_ = v_val_543_;
goto v___jp_507_;
}
}
v___jp_544_:
{
lean_object* v_toCold_548_; lean_object* v_ref_549_; uint8_t v_suppressElabErrors_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v_ref_554_; lean_object* v___x_555_; 
v_toCold_548_ = lean_ctor_get(v___y_467_, 0);
v_ref_549_ = lean_ctor_get(v___y_467_, 2);
v_suppressElabErrors_550_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*3 + 2);
v___x_551_ = lean_box(v_suppressElabErrors_550_);
v___x_552_ = lean_box(v___y_545_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_553_, 0, v___x_551_);
lean_closure_set(v___f_553_, 1, v___x_552_);
v_ref_554_ = l_Lean_replaceRef(v_ref_461_, v_ref_549_);
v___x_555_ = l_Lean_Syntax_getPos_x3f(v_ref_554_, v___y_546_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___y_535_ = v_toCold_548_;
v___y_536_ = v___f_553_;
v___y_537_ = v_suppressElabErrors_550_;
v___y_538_ = v_ref_554_;
v___y_539_ = v___y_547_;
v___y_540_ = v___y_546_;
v___y_541_ = v___x_556_;
goto v___jp_534_;
}
else
{
lean_object* v_val_557_; 
v_val_557_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v___x_555_, 1);
v___y_535_ = v_toCold_548_;
v___y_536_ = v___f_553_;
v___y_537_ = v_suppressElabErrors_550_;
v___y_538_ = v_ref_554_;
v___y_539_ = v___y_547_;
v___y_540_ = v___y_546_;
v___y_541_ = v_val_557_;
goto v___jp_534_;
}
}
v___jp_559_:
{
if (v___y_562_ == 0)
{
v___y_545_ = v___y_560_;
v___y_546_ = v___y_561_;
v___y_547_ = v_severity_463_;
goto v___jp_544_;
}
else
{
v___y_545_ = v___y_560_;
v___y_546_ = v___y_561_;
v___y_547_ = v___x_558_;
goto v___jp_544_;
}
}
v___jp_563_:
{
if (v___y_564_ == 0)
{
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 1;
v___x_566_ = l_Lean_instBEqMessageSeverity_beq(v_severity_463_, v___x_565_);
if (v___x_566_ == 0)
{
v___y_560_ = v___y_564_;
v___y_561_ = v___y_564_;
v___y_562_ = v___x_566_;
goto v___jp_559_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_467_);
v___x_568_ = l_Lean_warningAsError;
v___x_569_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit_spec__0(v___x_567_, v___x_568_);
lean_dec_ref(v___x_567_);
v___y_560_ = v___y_564_;
v___y_561_ = v___y_564_;
v___y_562_ = v___x_569_;
goto v___jp_559_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_msgData_462_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_574_, lean_object* v_msgData_575_, lean_object* v_severity_576_, lean_object* v_isSilent_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_severity_boxed_583_; uint8_t v_isSilent_boxed_584_; lean_object* v_res_585_; 
v_severity_boxed_583_ = lean_unbox(v_severity_576_);
v_isSilent_boxed_584_ = lean_unbox(v_isSilent_577_);
v_res_585_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_574_, v_msgData_575_, v_severity_boxed_583_, v_isSilent_boxed_584_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v_ref_574_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_586_, uint8_t v_severity_587_, uint8_t v_isSilent_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_ref_599_; lean_object* v___x_600_; 
v_ref_599_ = lean_ctor_get(v___y_596_, 2);
v___x_600_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_599_, v_msgData_586_, v_severity_587_, v_isSilent_588_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_601_, lean_object* v_severity_602_, lean_object* v_isSilent_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v_severity_boxed_614_; uint8_t v_isSilent_boxed_615_; lean_object* v_res_616_; 
v_severity_boxed_614_ = lean_unbox(v_severity_602_);
v_isSilent_boxed_615_ = lean_unbox(v_isSilent_603_);
v_res_616_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_601_, v_severity_boxed_614_, v_isSilent_boxed_615_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_msgData_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = 1;
v___x_629_ = 0;
v___x_630_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_617_, v___x_628_, v___x_629_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_msgData_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__9));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__11));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v___x_661_, lean_object* v_stx_662_, uint8_t v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v_a_673_, lean_object* v_params_674_, lean_object* v_____x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_suggestions_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_909_; 
v_fst_737_ = lean_ctor_get(v_____x_675_, 0);
v_snd_738_ = lean_ctor_get(v_____x_675_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_____x_675_);
if (v_isSharedCheck_909_ == 0)
{
v___x_740_ = v_____x_675_;
v_isShared_741_ = v_isSharedCheck_909_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_inc(v_fst_737_);
lean_dec(v_____x_675_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_909_;
goto v_resetjp_739_;
}
v___jp_686_:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_array_get_size(v_suggestions_687_);
v___x_691_ = lean_nat_dec_eq(v___x_690_, v___x_661_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_692_ = lean_box(0);
v___x_693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_694_ = 4;
v___x_695_ = l_Lean_MessageData_nil;
v___x_696_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_662_, v_suggestions_687_, v___x_692_, v___x_693_, v___x_692_, v___x_694_, v___x_695_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_705_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_box(v___x_663_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_696_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_696_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_714_ = lean_array_get(v___x_664_, v_suggestions_687_, v___x_665_);
lean_dec_ref(v_suggestions_687_);
v___x_715_ = lean_box(0);
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_717_ = 4;
v___x_718_ = l_Lean_MessageData_nil;
v___x_719_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_662_, v___x_714_, v___x_715_, v___x_716_, v___x_715_, v___x_717_, v___x_718_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_728_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_box(v___x_663_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_719_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_719_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
v_resetjp_739_:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_Grind_Action_run(v_snd_738_, v_a_666_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
if (lean_obj_tag(v_a_743_) == 0)
{
lean_object* v_seq_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_851_; 
v_seq_744_ = lean_ctor_get(v_a_743_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_743_);
if (v_isSharedCheck_851_ == 0)
{
v___x_746_ = v_a_743_;
v_isShared_747_ = v_isSharedCheck_851_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_seq_744_);
lean_dec(v_a_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_851_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_List_appendTR___redArg(v_fst_737_, v_seq_744_);
lean_inc(v___x_748_);
v___x_749_ = l_Lean_Meta_Grind_mkFinishTactic(v___x_748_, v_a_667_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v_suggestions_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_suggestions_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___x_834_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
lean_inc_n(v___x_748_, 2);
v___x_751_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v___x_748_);
v___x_811_ = lean_mk_empty_array_with_capacity(v___x_665_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_a_673_);
lean_inc_ref(v_a_668_);
lean_inc_ref(v___x_812_);
v___x_834_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_812_, v_a_668_, v___x_748_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_836_ == 0)
{
v_suggestions_814_ = v___x_811_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
v___y_823_ = v___y_684_;
goto v___jp_813_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
lean_inc_ref(v___x_672_);
lean_inc_ref(v___x_671_);
lean_inc_ref(v___x_670_);
lean_inc_ref(v___x_669_);
v___x_838_ = l_Lean_Name_mkStr5(v___x_669_, v___x_670_, v___x_671_, v___x_672_, v___x_837_);
lean_inc(v___x_751_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_751_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
lean_ctor_set(v___x_841_, 2, v___x_840_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
lean_ctor_set(v___x_841_, 4, v___x_840_);
lean_ctor_set(v___x_841_, 5, v___x_840_);
v___x_842_ = lean_array_push(v___x_811_, v___x_841_);
v_suggestions_814_ = v___x_842_;
v___y_815_ = v___y_676_;
v___y_816_ = v___y_677_;
v___y_817_ = v___y_678_;
v___y_818_ = v___y_679_;
v___y_819_ = v___y_680_;
v___y_820_ = v___y_681_;
v___y_821_ = v___y_682_;
v___y_822_ = v___y_683_;
v___y_823_ = v___y_684_;
goto v___jp_813_;
}
}
else
{
lean_dec_ref_known(v___x_812_, 1);
lean_dec_ref(v___x_811_);
lean_dec(v___x_751_);
lean_dec(v_a_750_);
lean_dec(v___x_748_);
lean_del_object(v___x_746_);
lean_del_object(v___x_740_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
return v___x_834_;
}
v___jp_752_:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_get_size(v_suggestions_753_);
v___x_764_ = lean_nat_dec_eq(v___x_763_, v___x_665_);
if (v___x_764_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v___x_748_);
lean_del_object(v___x_746_);
lean_del_object(v___x_740_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
v_suggestions_687_ = v_suggestions_753_;
v___y_688_ = v___y_761_;
v___y_689_ = v___y_762_;
goto v___jp_686_;
}
else
{
lean_object* v___x_765_; 
lean_dec_ref(v_suggestions_753_);
v___x_765_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v___x_748_, v___y_761_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v_mvarId_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_801_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_mvarId_767_ = lean_ctor_get(v_a_668_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_668_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_a_668_, 0);
lean_dec(v_unused_802_);
v___x_769_ = v_a_668_;
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_mvarId_767_);
lean_dec(v_a_668_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_771_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3);
v___x_772_ = l_Lean_MessageData_ofSyntax(v_a_766_);
v___x_773_ = l_Lean_indentD(v___x_772_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 7);
lean_ctor_set(v___x_769_, 1, v___x_773_);
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_775_ = v___x_769_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_800_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 7);
lean_ctor_set(v___x_740_, 1, v___x_776_);
lean_ctor_set(v___x_740_, 0, v___x_775_);
v___x_778_ = v___x_740_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_799_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 0, v_mvarId_767_);
v___x_780_ = v___x_746_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_mvarId_767_);
v___x_780_ = v_reuseFailAlloc_798_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v___x_781_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_782_, 1);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6));
v___x_784_ = l_Lean_Name_mkStr5(v___x_669_, v___x_670_, v___x_671_, v___x_672_, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_751_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
lean_ctor_set(v___x_787_, 2, v___x_786_);
lean_ctor_set(v___x_787_, 3, v___x_786_);
lean_ctor_set(v___x_787_, 4, v___x_786_);
lean_ctor_set(v___x_787_, 5, v___x_786_);
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_661_);
v___x_789_ = lean_array_push(v___x_788_, v___x_787_);
v_suggestions_687_ = v___x_789_;
v___y_688_ = v___y_761_;
v___y_689_ = v___y_762_;
goto v___jp_686_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v___x_751_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v_stx_662_);
v_a_790_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_782_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_782_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
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
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v___x_751_);
lean_del_object(v___x_746_);
lean_del_object(v___x_740_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
v_a_803_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_765_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_765_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
v___jp_813_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = lean_box(0);
lean_inc(v_a_750_);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v_a_750_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
lean_inc_ref(v_a_668_);
v___x_826_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_812_, v_a_668_, v___x_825_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; uint8_t v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v___x_828_ = lean_unbox(v_a_827_);
lean_dec(v_a_827_);
if (v___x_828_ == 0)
{
lean_dec(v_a_750_);
v_suggestions_753_ = v_suggestions_814_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
v___y_762_ = v___y_823_;
goto v___jp_752_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8));
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_a_750_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
lean_ctor_set(v___x_832_, 3, v___x_831_);
lean_ctor_set(v___x_832_, 4, v___x_831_);
lean_ctor_set(v___x_832_, 5, v___x_831_);
v___x_833_ = lean_array_push(v_suggestions_814_, v___x_832_);
v_suggestions_753_ = v___x_833_;
v___y_754_ = v___y_815_;
v___y_755_ = v___y_816_;
v___y_756_ = v___y_817_;
v___y_757_ = v___y_818_;
v___y_758_ = v___y_819_;
v___y_759_ = v___y_820_;
v___y_760_ = v___y_821_;
v___y_761_ = v___y_822_;
v___y_762_ = v___y_823_;
goto v___jp_752_;
}
}
else
{
lean_dec_ref(v_suggestions_814_);
lean_dec(v___x_751_);
lean_dec(v_a_750_);
lean_dec(v___x_748_);
lean_del_object(v___x_746_);
lean_del_object(v___x_740_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
return v___x_826_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v___x_748_);
lean_del_object(v___x_746_);
lean_del_object(v___x_740_);
lean_dec_ref(v_a_673_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
v_a_843_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_749_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_749_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v_gs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_900_; 
lean_del_object(v___x_740_);
lean_dec(v_fst_737_);
lean_dec_ref(v_a_673_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
v_gs_852_ = lean_ctor_get(v_a_743_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_a_743_);
if (v_isSharedCheck_900_ == 0)
{
v___x_854_ = v_a_743_;
v_isShared_855_ = v_isSharedCheck_900_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_gs_852_);
lean_dec(v_a_743_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_900_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
if (lean_obj_tag(v_gs_852_) == 1)
{
lean_object* v_head_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_896_; 
v_head_856_ = lean_ctor_get(v_gs_852_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_gs_852_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_gs_852_, 1);
lean_dec(v_unused_897_);
v___x_858_ = v_gs_852_;
v_isShared_859_ = v_isSharedCheck_896_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_head_856_);
lean_dec(v_gs_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_896_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v_head_856_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_head_856_);
v___x_861_ = v_reuseFailAlloc_895_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_mkResult(v_params_674_, v___x_861_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_863_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__10);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 7);
lean_ctor_set(v___x_858_, 1, v_a_865_);
lean_ctor_set(v___x_858_, 0, v___x_866_);
v___x_868_ = v___x_858_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_a_865_);
v___x_868_ = v_reuseFailAlloc_878_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v___x_869_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_868_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_858_);
v_a_879_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_864_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_864_);
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
lean_del_object(v___x_858_);
v_a_887_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_862_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_862_);
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
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_del_object(v___x_854_);
lean_dec(v_gs_852_);
v___x_898_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__12);
v___x_899_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v___x_898_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_740_);
lean_dec(v_fst_737_);
lean_dec_ref(v_a_673_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_stx_662_);
v_a_901_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_742_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_742_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v___x_910_ = _args[0];
lean_object* v_stx_911_ = _args[1];
lean_object* v___x_912_ = _args[2];
lean_object* v___x_913_ = _args[3];
lean_object* v___x_914_ = _args[4];
lean_object* v_a_915_ = _args[5];
lean_object* v_a_916_ = _args[6];
lean_object* v_a_917_ = _args[7];
lean_object* v___x_918_ = _args[8];
lean_object* v___x_919_ = _args[9];
lean_object* v___x_920_ = _args[10];
lean_object* v___x_921_ = _args[11];
lean_object* v_a_922_ = _args[12];
lean_object* v_params_923_ = _args[13];
lean_object* v_____x_924_ = _args[14];
lean_object* v___y_925_ = _args[15];
lean_object* v___y_926_ = _args[16];
lean_object* v___y_927_ = _args[17];
lean_object* v___y_928_ = _args[18];
lean_object* v___y_929_ = _args[19];
lean_object* v___y_930_ = _args[20];
lean_object* v___y_931_ = _args[21];
lean_object* v___y_932_ = _args[22];
lean_object* v___y_933_ = _args[23];
lean_object* v___y_934_ = _args[24];
_start:
{
uint8_t v___x_49234__boxed_935_; lean_object* v_res_936_; 
v___x_49234__boxed_935_ = lean_unbox(v___x_912_);
v_res_936_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v___x_910_, v_stx_911_, v___x_49234__boxed_935_, v___x_913_, v___x_914_, v_a_915_, v_a_916_, v_a_917_, v___x_918_, v___x_919_, v___x_920_, v___x_921_, v_a_922_, v_params_923_, v_____x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v_params_923_);
lean_dec_ref(v_a_916_);
lean_dec(v___x_914_);
lean_dec_ref(v___x_913_);
lean_dec(v___x_910_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(uint8_t v_sym_937_, lean_object* v_a_938_, lean_object* v___f_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
if (v_sym_937_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_a_938_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
v___x_952_ = lean_apply_11(v___f_939_, v___x_951_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, lean_box(0));
return v___x_952_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit(v_a_938_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
v___x_955_ = lean_apply_11(v___f_939_, v_a_954_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, lean_box(0));
return v___x_955_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v___f_939_);
v_a_956_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_953_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v_sym_964_, lean_object* v_a_965_, lean_object* v___f_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v_sym_boxed_977_; lean_object* v_res_978_; 
v_sym_boxed_977_ = lean_unbox(v_sym_964_);
v_res_978_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v_sym_boxed_977_, v_a_965_, v___f_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___y_979_, v___y_980_, v___y_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1001_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_del_object(v___x_992_);
v___x_999_ = lean_box(0);
v___x_1000_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_999_, v___y_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_1000_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_989_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_989_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v_stx_1023_, uint8_t v___x_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_a_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_ref_1043_; lean_object* v___x_1044_; 
v_ref_1043_ = lean_ctor_get(v___y_1040_, 2);
v___x_1044_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1021_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1035_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v_params_1048_; uint8_t v_sym_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___y_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_params_1048_ = lean_ctor_get(v___y_1034_, 4);
v_sym_1049_ = lean_ctor_get_uint8(v___y_1034_, sizeof(void*)*5);
v___x_1050_ = lean_box(v___x_1024_);
lean_inc_ref(v_params_1048_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 25, 14);
lean_closure_set(v___f_1051_, 0, v___x_1022_);
lean_closure_set(v___f_1051_, 1, v_stx_1023_);
lean_closure_set(v___f_1051_, 2, v___x_1050_);
lean_closure_set(v___f_1051_, 3, v___x_1025_);
lean_closure_set(v___f_1051_, 4, v___x_1026_);
lean_closure_set(v___f_1051_, 5, v_a_1045_);
lean_closure_set(v___f_1051_, 6, v_a_1027_);
lean_closure_set(v___f_1051_, 7, v_a_1028_);
lean_closure_set(v___f_1051_, 8, v___x_1029_);
lean_closure_set(v___f_1051_, 9, v___x_1030_);
lean_closure_set(v___f_1051_, 10, v___x_1031_);
lean_closure_set(v___f_1051_, 11, v___x_1032_);
lean_closure_set(v___f_1051_, 12, v_a_1033_);
lean_closure_set(v___f_1051_, 13, v_params_1048_);
v___x_1052_ = lean_box(v_sym_1049_);
v___y_1053_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 13, 3);
lean_closure_set(v___y_1053_, 0, v___x_1052_);
lean_closure_set(v___y_1053_, 1, v_a_1047_);
lean_closure_set(v___y_1053_, 2, v___f_1051_);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1054_, 0, v___y_1053_);
v___x_1055_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1054_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec_ref(v___y_1034_);
return v___x_1055_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1045_);
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_a_1033_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v___x_1026_);
lean_dec_ref(v___x_1025_);
lean_dec(v_stx_1023_);
lean_dec(v___x_1022_);
v_a_1056_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1046_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1046_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_a_1033_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v___x_1026_);
lean_dec_ref(v___x_1025_);
lean_dec(v_stx_1023_);
lean_dec(v___x_1022_);
v_a_1064_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v___x_1044_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1044_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1068_ = lean_io_error_to_string(v_a_1064_);
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_ofFormat(v___x_1069_);
lean_inc(v_ref_1043_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_ref_1043_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1071_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___x_1076_ = _args[0];
lean_object* v___x_1077_ = _args[1];
lean_object* v_stx_1078_ = _args[2];
lean_object* v___x_1079_ = _args[3];
lean_object* v___x_1080_ = _args[4];
lean_object* v___x_1081_ = _args[5];
lean_object* v_a_1082_ = _args[6];
lean_object* v_a_1083_ = _args[7];
lean_object* v___x_1084_ = _args[8];
lean_object* v___x_1085_ = _args[9];
lean_object* v___x_1086_ = _args[10];
lean_object* v___x_1087_ = _args[11];
lean_object* v_a_1088_ = _args[12];
lean_object* v___y_1089_ = _args[13];
lean_object* v___y_1090_ = _args[14];
lean_object* v___y_1091_ = _args[15];
lean_object* v___y_1092_ = _args[16];
lean_object* v___y_1093_ = _args[17];
lean_object* v___y_1094_ = _args[18];
lean_object* v___y_1095_ = _args[19];
lean_object* v___y_1096_ = _args[20];
lean_object* v___y_1097_ = _args[21];
_start:
{
uint8_t v___x_49905__boxed_1098_; lean_object* v_res_1099_; 
v___x_49905__boxed_1098_ = lean_unbox(v___x_1079_);
v_res_1099_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___x_1076_, v___x_1077_, v_stx_1078_, v___x_49905__boxed_1098_, v___x_1080_, v___x_1081_, v_a_1082_, v_a_1083_, v___x_1084_, v___x_1085_, v___x_1086_, v___x_1087_, v_a_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v_stx_1103_, uint8_t v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v_only_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v___x_1101_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1113_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___closed__0));
v___x_1126_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1125_, v___y_1112_, v___y_1113_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_params_1128_; uint8_t v___y_1130_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v_params_1128_ = lean_ctor_get(v___y_1112_, 4);
lean_inc_ref(v_params_1128_);
if (lean_obj_tag(v_only_1111_) == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = 0;
v___y_1130_ = v___x_1135_;
goto v___jp_1129_;
}
else
{
v___y_1130_ = v___x_1104_;
goto v___jp_1129_;
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_unsigned_to_nat(10000u);
v___x_1132_ = lean_box(v___x_1104_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 22, 13);
lean_closure_set(v___f_1133_, 0, v___x_1131_);
lean_closure_set(v___f_1133_, 1, v___x_1102_);
lean_closure_set(v___f_1133_, 2, v_stx_1103_);
lean_closure_set(v___f_1133_, 3, v___x_1132_);
lean_closure_set(v___f_1133_, 4, v___x_1105_);
lean_closure_set(v___f_1133_, 5, v___x_1106_);
lean_closure_set(v___f_1133_, 6, v_a_1122_);
lean_closure_set(v___f_1133_, 7, v_a_1124_);
lean_closure_set(v___f_1133_, 8, v___x_1107_);
lean_closure_set(v___f_1133_, 9, v___x_1108_);
lean_closure_set(v___f_1133_, 10, v___x_1109_);
lean_closure_set(v___f_1133_, 11, v___x_1110_);
lean_closure_set(v___f_1133_, 12, v_a_1127_);
v___x_1134_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_1128_, v___x_1101_, v___y_1130_, v___f_1133_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___y_1112_);
return v___x_1134_;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1124_);
lean_dec(v_a_1122_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v_stx_1103_);
lean_dec(v___x_1102_);
v_a_1136_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1126_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1122_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v_stx_1103_);
lean_dec(v___x_1102_);
v_a_1144_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1123_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1123_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec(v___x_1106_);
lean_dec_ref(v___x_1105_);
lean_dec(v_stx_1103_);
lean_dec(v___x_1102_);
v_a_1152_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1121_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1121_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed(lean_object** _args){
lean_object* v___x_1160_ = _args[0];
lean_object* v___x_1161_ = _args[1];
lean_object* v_stx_1162_ = _args[2];
lean_object* v___x_1163_ = _args[3];
lean_object* v___x_1164_ = _args[4];
lean_object* v___x_1165_ = _args[5];
lean_object* v___x_1166_ = _args[6];
lean_object* v___x_1167_ = _args[7];
lean_object* v___x_1168_ = _args[8];
lean_object* v___x_1169_ = _args[9];
lean_object* v_only_1170_ = _args[10];
lean_object* v___y_1171_ = _args[11];
lean_object* v___y_1172_ = _args[12];
lean_object* v___y_1173_ = _args[13];
lean_object* v___y_1174_ = _args[14];
lean_object* v___y_1175_ = _args[15];
lean_object* v___y_1176_ = _args[16];
lean_object* v___y_1177_ = _args[17];
lean_object* v___y_1178_ = _args[18];
lean_object* v___y_1179_ = _args[19];
_start:
{
uint8_t v___x_50030__boxed_1180_; lean_object* v_res_1181_; 
v___x_50030__boxed_1180_ = lean_unbox(v___x_1163_);
v_res_1181_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4(v___x_1160_, v___x_1161_, v_stx_1162_, v___x_50030__boxed_1180_, v___x_1164_, v___x_1165_, v___x_1166_, v___x_1167_, v___x_1168_, v___x_1169_, v_only_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v_only_1170_);
lean_dec_ref(v___x_1160_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_bs_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_usize_dec_lt(v_i_1183_, v_sz_1182_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_bs_1184_);
return v___x_1186_;
}
else
{
lean_object* v_v_1187_; lean_object* v___x_1188_; lean_object* v_bs_x27_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v_v_1187_ = lean_array_uget(v_bs_1184_, v_i_1183_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v_bs_x27_1189_ = lean_array_uset(v_bs_1184_, v_i_1183_, v___x_1188_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1183_, v___x_1190_);
v___x_1192_ = lean_array_uset(v_bs_x27_1189_, v_i_1183_, v_v_1187_);
v_i_1183_ = v___x_1191_;
v_bs_1184_ = v___x_1192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_1194_, lean_object* v_i_1195_, lean_object* v_bs_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1194_);
lean_dec(v_sz_1194_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1195_);
lean_dec(v_i_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1197_, v_i_boxed_1198_, v_bs_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__0));
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__1));
v___x_1221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__2));
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_symInit___closed__3));
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
lean_inc(v_stx_1209_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v_stx_1209_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_stx_1209_);
v___x_1225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; size_t v_sz_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = l_Lean_Syntax_getArg(v_stx_1209_, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_getArgs(v___x_1227_);
lean_dec(v___x_1227_);
v_sz_1229_ = lean_array_size(v___x_1228_);
v___x_1230_ = ((size_t)0ULL);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1229_, v___x_1230_, v___x_1228_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_stx_1209_);
v___x_1232_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1232_;
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1282_; 
v_val_1233_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1235_ = v___x_1231_;
v_isShared_1236_ = v_isSharedCheck_1282_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1282_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v_only_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1237_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_unsigned_to_nat(2u);
v___x_1273_ = l_Lean_Syntax_getArg(v_stx_1209_, v___x_1272_);
v___x_1274_ = l_Lean_Syntax_isNone(v___x_1273_);
if (v___x_1274_ == 0)
{
uint8_t v___x_1275_; 
lean_inc(v___x_1273_);
v___x_1275_ = l_Lean_Syntax_matchesNull(v___x_1273_, v___x_1226_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v___x_1273_);
lean_del_object(v___x_1235_);
lean_dec(v_val_1233_);
lean_dec(v_stx_1209_);
v___x_1276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1276_;
}
else
{
lean_object* v_only_1277_; lean_object* v___x_1279_; 
v_only_1277_ = l_Lean_Syntax_getArg(v___x_1273_, v___x_1238_);
lean_dec(v___x_1273_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_only_1277_);
v___x_1279_ = v___x_1235_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_only_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v_only_1255_ = v___x_1279_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
v___y_1262_ = v_a_1216_;
v___y_1263_ = v_a_1217_;
goto v___jp_1254_;
}
}
}
else
{
lean_object* v___x_1281_; 
lean_dec(v___x_1273_);
lean_del_object(v___x_1235_);
v___x_1281_ = lean_box(0);
v_only_1255_ = v___x_1281_;
v___y_1256_ = v_a_1210_;
v___y_1257_ = v_a_1211_;
v___y_1258_ = v_a_1212_;
v___y_1259_ = v_a_1213_;
v___y_1260_ = v_a_1214_;
v___y_1261_ = v_a_1215_;
v___y_1262_ = v_a_1216_;
v___y_1263_ = v_a_1217_;
goto v___jp_1254_;
}
v___jp_1239_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; 
v___x_1250_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1249_);
lean_dec_ref(v___y_1249_);
v___x_1251_ = lean_box(v___x_1224_);
v___f_1252_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1252_, 0, v___x_1250_);
lean_closure_set(v___f_1252_, 1, v___x_1226_);
lean_closure_set(v___f_1252_, 2, v_stx_1209_);
lean_closure_set(v___f_1252_, 3, v___x_1251_);
lean_closure_set(v___f_1252_, 4, v___x_1237_);
lean_closure_set(v___f_1252_, 5, v___x_1238_);
lean_closure_set(v___f_1252_, 6, v___x_1219_);
lean_closure_set(v___f_1252_, 7, v___x_1220_);
lean_closure_set(v___f_1252_, 8, v___x_1221_);
lean_closure_set(v___f_1252_, 9, v___x_1222_);
lean_closure_set(v___f_1252_, 10, v___y_1240_);
v___x_1253_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_1233_, v___f_1252_, v___y_1248_, v___y_1244_, v___y_1243_, v___y_1246_, v___y_1242_, v___y_1241_, v___y_1245_, v___y_1247_);
return v___x_1253_;
}
v___jp_1254_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_unsigned_to_nat(3u);
v___x_1265_ = l_Lean_Syntax_getArg(v_stx_1209_, v___x_1264_);
v___x_1266_ = l_Lean_Syntax_isNone(v___x_1265_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
lean_inc(v___x_1265_);
v___x_1267_ = l_Lean_Syntax_matchesNull(v___x_1265_, v___x_1264_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v___x_1265_);
lean_dec(v_only_1255_);
lean_dec(v_val_1233_);
lean_dec(v_stx_1209_);
v___x_1268_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v_params_x3f_1270_; 
v___x_1269_ = l_Lean_Syntax_getArg(v___x_1265_, v___x_1226_);
lean_dec(v___x_1265_);
v_params_x3f_1270_ = l_Lean_Syntax_getArgs(v___x_1269_);
lean_dec(v___x_1269_);
v___y_1240_ = v_only_1255_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1260_;
v___y_1243_ = v___y_1258_;
v___y_1244_ = v___y_1257_;
v___y_1245_ = v___y_1262_;
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1263_;
v___y_1248_ = v___y_1256_;
v___y_1249_ = v_params_x3f_1270_;
goto v___jp_1239_;
}
}
else
{
lean_object* v___x_1271_; 
lean_dec(v___x_1265_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___y_1240_ = v_only_1255_;
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1260_;
v___y_1243_ = v___y_1258_;
v___y_1244_ = v___y_1257_;
v___y_1245_ = v___y_1262_;
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1263_;
v___y_1248_ = v___y_1256_;
v___y_1249_ = v___x_1271_;
goto v___jp_1239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(lean_object* v_00_u03b1_1294_, lean_object* v_msg_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___redArg(v_msg_1295_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__3(v_00_u03b1_1307_, v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(lean_object* v_ref_1320_, lean_object* v_msgData_1321_, uint8_t v_severity_1322_, uint8_t v_isSilent_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___redArg(v_ref_1320_, v_msgData_1321_, v_severity_1322_, v_isSilent_1323_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_1335_, lean_object* v_msgData_1336_, lean_object* v_severity_1337_, lean_object* v_isSilent_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_severity_boxed_1349_; uint8_t v_isSilent_boxed_1350_; lean_object* v_res_1351_; 
v_severity_boxed_1349_ = lean_unbox(v_severity_1337_);
v_isSilent_boxed_1350_ = lean_unbox(v_isSilent_1338_);
v_res_1351_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2_spec__3(v_ref_1335_, v_msgData_1336_, v_severity_boxed_1349_, v_isSilent_boxed_1350_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v_ref_1335_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1392_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_1394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14));
v___x_1395_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_1396_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_1398_;
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
