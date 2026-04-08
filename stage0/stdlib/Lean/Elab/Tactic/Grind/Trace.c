// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Trace
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.Config import Lean.Elab.Tactic.Grind.Param import Lean.Meta.Tactic.TryThis import Lean.Meta.Tactic.Grind.Finish import Lean.Meta.Tactic.Grind.CollectParams
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkFinish(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkFinishTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`finish\?` failed\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`finish\?` failed, but resulting goal is not available"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "finishTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 104, 221, 59, 99, 114, 168, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(186, 27, 67, 52, 119, 51, 108, 2)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(91, 188, 82, 28, 141, 159, 228, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 23, 221, 94, 250, 9, 160, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 10, 68, 183, 25, 215, 244, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 13, 146, 144, 74, 183, 56, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 20, 224, 46, 151, 65, 68, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalFinishTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(30, 0, 151, 159, 220, 77, 241, 66)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(lean_object* v_x_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_ctx_11_; lean_object* v_config_12_; lean_object* v_toContext_13_; lean_object* v_sctx_14_; lean_object* v_methods_15_; lean_object* v_params_16_; uint8_t v_sym_17_; lean_object* v_simp_18_; lean_object* v_simpMethods_19_; lean_object* v_anchorRefs_x3f_20_; uint8_t v_cheapCases_21_; uint8_t v_reportMVarIssue_22_; lean_object* v_splitSource_23_; lean_object* v_symPrios_24_; lean_object* v_extensions_25_; uint8_t v_debug_26_; uint8_t v_markInstances_27_; uint8_t v_lax_28_; uint8_t v_suggestions_29_; uint8_t v_locals_30_; lean_object* v_splits_31_; lean_object* v_ematch_32_; lean_object* v_gen_33_; lean_object* v_instances_34_; uint8_t v_matchEqs_35_; uint8_t v_splitMatch_36_; uint8_t v_splitIte_37_; uint8_t v_splitIndPred_38_; uint8_t v_splitImp_39_; lean_object* v_canonHeartbeats_40_; uint8_t v_ext_41_; uint8_t v_extAll_42_; uint8_t v_etaStruct_43_; uint8_t v_funext_44_; uint8_t v_lookahead_45_; uint8_t v_verbose_46_; uint8_t v_clean_47_; uint8_t v_qlia_48_; uint8_t v_mbtc_49_; uint8_t v_zetaDelta_50_; uint8_t v_zeta_51_; uint8_t v_ring_52_; lean_object* v_ringSteps_53_; uint8_t v_linarith_54_; uint8_t v_lia_55_; uint8_t v_ac_56_; lean_object* v_acSteps_57_; lean_object* v_exp_58_; uint8_t v_abstractProof_59_; uint8_t v_inj_60_; uint8_t v_order_61_; lean_object* v_min_62_; lean_object* v_detailed_63_; uint8_t v_useSorry_64_; uint8_t v_revert_65_; uint8_t v_funCC_66_; uint8_t v_reducible_67_; lean_object* v_maxSuggestions_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_ctx_11_ = lean_ctor_get(v_a_2_, 1);
v_config_12_ = lean_ctor_get(v_ctx_11_, 2);
v_toContext_13_ = lean_ctor_get(v_a_2_, 0);
v_sctx_14_ = lean_ctor_get(v_a_2_, 2);
v_methods_15_ = lean_ctor_get(v_a_2_, 3);
v_params_16_ = lean_ctor_get(v_a_2_, 4);
v_sym_17_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*5);
v_simp_18_ = lean_ctor_get(v_ctx_11_, 0);
v_simpMethods_19_ = lean_ctor_get(v_ctx_11_, 1);
v_anchorRefs_x3f_20_ = lean_ctor_get(v_ctx_11_, 3);
v_cheapCases_21_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*7);
v_reportMVarIssue_22_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*7 + 1);
v_splitSource_23_ = lean_ctor_get(v_ctx_11_, 4);
v_symPrios_24_ = lean_ctor_get(v_ctx_11_, 5);
v_extensions_25_ = lean_ctor_get(v_ctx_11_, 6);
v_debug_26_ = lean_ctor_get_uint8(v_ctx_11_, sizeof(void*)*7 + 2);
v_markInstances_27_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 1);
v_lax_28_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 2);
v_suggestions_29_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 3);
v_locals_30_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 4);
v_splits_31_ = lean_ctor_get(v_config_12_, 0);
v_ematch_32_ = lean_ctor_get(v_config_12_, 1);
v_gen_33_ = lean_ctor_get(v_config_12_, 2);
v_instances_34_ = lean_ctor_get(v_config_12_, 3);
v_matchEqs_35_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 5);
v_splitMatch_36_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 6);
v_splitIte_37_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 7);
v_splitIndPred_38_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 8);
v_splitImp_39_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 9);
v_canonHeartbeats_40_ = lean_ctor_get(v_config_12_, 4);
v_ext_41_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 10);
v_extAll_42_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 11);
v_etaStruct_43_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 12);
v_funext_44_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 13);
v_lookahead_45_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 14);
v_verbose_46_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 15);
v_clean_47_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 16);
v_qlia_48_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 17);
v_mbtc_49_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 18);
v_zetaDelta_50_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 19);
v_zeta_51_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 20);
v_ring_52_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 21);
v_ringSteps_53_ = lean_ctor_get(v_config_12_, 5);
v_linarith_54_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 22);
v_lia_55_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 23);
v_ac_56_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 24);
v_acSteps_57_ = lean_ctor_get(v_config_12_, 6);
v_exp_58_ = lean_ctor_get(v_config_12_, 7);
v_abstractProof_59_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 25);
v_inj_60_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 26);
v_order_61_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 27);
v_min_62_ = lean_ctor_get(v_config_12_, 8);
v_detailed_63_ = lean_ctor_get(v_config_12_, 9);
v_useSorry_64_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 28);
v_revert_65_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 29);
v_funCC_66_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 30);
v_reducible_67_ = lean_ctor_get_uint8(v_config_12_, sizeof(void*)*11 + 31);
v_maxSuggestions_68_ = lean_ctor_get(v_config_12_, 10);
v___x_69_ = 1;
lean_inc(v_maxSuggestions_68_);
lean_inc(v_detailed_63_);
lean_inc(v_min_62_);
lean_inc(v_exp_58_);
lean_inc(v_acSteps_57_);
lean_inc(v_ringSteps_53_);
lean_inc(v_canonHeartbeats_40_);
lean_inc(v_instances_34_);
lean_inc(v_gen_33_);
lean_inc(v_ematch_32_);
lean_inc(v_splits_31_);
v___x_70_ = lean_alloc_ctor(0, 11, 32);
lean_ctor_set(v___x_70_, 0, v_splits_31_);
lean_ctor_set(v___x_70_, 1, v_ematch_32_);
lean_ctor_set(v___x_70_, 2, v_gen_33_);
lean_ctor_set(v___x_70_, 3, v_instances_34_);
lean_ctor_set(v___x_70_, 4, v_canonHeartbeats_40_);
lean_ctor_set(v___x_70_, 5, v_ringSteps_53_);
lean_ctor_set(v___x_70_, 6, v_acSteps_57_);
lean_ctor_set(v___x_70_, 7, v_exp_58_);
lean_ctor_set(v___x_70_, 8, v_min_62_);
lean_ctor_set(v___x_70_, 9, v_detailed_63_);
lean_ctor_set(v___x_70_, 10, v_maxSuggestions_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11, v___x_69_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 1, v_markInstances_27_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 2, v_lax_28_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 3, v_suggestions_29_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 4, v_locals_30_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 5, v_matchEqs_35_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 6, v_splitMatch_36_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 7, v_splitIte_37_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 8, v_splitIndPred_38_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 9, v_splitImp_39_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 10, v_ext_41_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 11, v_extAll_42_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 12, v_etaStruct_43_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 13, v_funext_44_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 14, v_lookahead_45_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 15, v_verbose_46_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 16, v_clean_47_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 17, v_qlia_48_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 18, v_mbtc_49_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 19, v_zetaDelta_50_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 20, v_zeta_51_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 21, v_ring_52_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 22, v_linarith_54_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 23, v_lia_55_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 24, v_ac_56_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 25, v_abstractProof_59_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 26, v_inj_60_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 27, v_order_61_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 28, v_useSorry_64_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 29, v_revert_65_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 30, v_funCC_66_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*11 + 31, v_reducible_67_);
lean_inc_ref(v_extensions_25_);
lean_inc_ref(v_symPrios_24_);
lean_inc(v_splitSource_23_);
lean_inc(v_anchorRefs_x3f_20_);
lean_inc_ref(v_simpMethods_19_);
lean_inc_ref(v_simp_18_);
v___x_71_ = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(v___x_71_, 0, v_simp_18_);
lean_ctor_set(v___x_71_, 1, v_simpMethods_19_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
lean_ctor_set(v___x_71_, 3, v_anchorRefs_x3f_20_);
lean_ctor_set(v___x_71_, 4, v_splitSource_23_);
lean_ctor_set(v___x_71_, 5, v_symPrios_24_);
lean_ctor_set(v___x_71_, 6, v_extensions_25_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7, v_cheapCases_21_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7 + 1, v_reportMVarIssue_22_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7 + 2, v_debug_26_);
lean_inc_ref(v_params_16_);
lean_inc_ref(v_methods_15_);
lean_inc_ref(v_sctx_14_);
lean_inc_ref(v_toContext_13_);
v___x_72_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_72_, 0, v_toContext_13_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set(v___x_72_, 2, v_sctx_14_);
lean_ctor_set(v___x_72_, 3, v_methods_15_);
lean_ctor_set(v___x_72_, 4, v_params_16_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*5, v_sym_17_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
v___x_73_ = lean_apply_9(v_x_1_, v___x_72_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(lean_object* v_00_u03b1_85_, lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v_x_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(lean_object* v_00_u03b1_97_, lean_object* v_x_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(v_00_u03b1_97_, v_x_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_108_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
v___x_110_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(lean_object* v_00_u03b1_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(lean_object* v_00_u03b1_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_env_146_; lean_object* v___x_147_; lean_object* v_mctx_148_; lean_object* v_lctx_149_; lean_object* v_options_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_env_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_146_);
lean_dec(v___x_145_);
v___x_147_ = lean_st_ref_get(v___y_141_);
v_mctx_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc_ref(v_mctx_148_);
lean_dec(v___x_147_);
v_lctx_149_ = lean_ctor_get(v___y_140_, 2);
v_options_150_ = lean_ctor_get(v___y_142_, 2);
lean_inc_ref(v_options_150_);
lean_inc_ref(v_lctx_149_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v_env_146_);
lean_ctor_set(v___x_151_, 1, v_mctx_148_);
lean_ctor_set(v___x_151_, 2, v_lctx_149_);
lean_ctor_set(v___x_151_, 3, v_options_150_);
v___x_152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_msgData_139_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(lean_object* v_msgData_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_ref_167_; lean_object* v___x_168_; lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_177_; 
v_ref_167_ = lean_ctor_get(v___y_164_, 5);
v___x_168_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msg_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_177_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
lean_inc(v_ref_167_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_ref_167_);
lean_ctor_set(v___x_173_, 1, v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 1);
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg___boxed(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_stx_203_, uint8_t v___x_204_, lean_object* v_params_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_saveState___redArg(v___y_208_, v___y_212_, v___y_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref(v___x_216_);
lean_inc_ref(v_a_197_);
v___x_218_ = l_Lean_Meta_Grind_Action_run(v_a_197_, v_a_198_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref(v___x_218_);
if (lean_obj_tag(v_a_219_) == 0)
{
lean_object* v_seq_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_300_; 
v_seq_220_ = lean_ctor_get(v_a_219_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_300_ == 0)
{
v___x_222_ = v_a_219_;
v_isShared_223_ = v_isSharedCheck_300_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_seq_220_);
lean_dec(v_a_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_300_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; 
lean_inc(v_seq_220_);
v___x_224_ = l_Lean_Meta_Grind_mkFinishTactic(v_seq_220_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v_a_217_);
v___x_227_ = v___x_222_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_217_);
v___x_227_ = v_reuseFailAlloc_291_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
lean_inc(v_a_225_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v_a_225_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Lean_Meta_Grind_Action_checkSeqAt(v___x_227_, v_a_197_, v___x_229_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v___x_232_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_seq_220_);
v___x_233_ = lean_unbox(v_a_231_);
lean_dec(v_a_231_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; 
lean_dec(v_a_225_);
v___x_234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_235_ = l_Lean_Name_mkStr5(v___x_199_, v___x_200_, v___x_201_, v___x_202_, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_ctor_set(v___x_238_, 3, v___x_237_);
lean_ctor_set(v___x_238_, 4, v___x_237_);
lean_ctor_set(v___x_238_, 5, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1));
v___x_240_ = 4;
v___x_241_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_203_, v___x_238_, v___x_237_, v___x_239_, v___x_237_, v___x_240_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; 
v_unused_250_ = lean_ctor_get(v___x_241_, 0);
lean_dec(v_unused_250_);
v___x_243_ = v___x_241_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_dec(v___x_241_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_box(v___x_204_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_241_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_241_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0));
v___x_260_ = l_Lean_Name_mkStr5(v___x_199_, v___x_200_, v___x_201_, v___x_202_, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_232_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v___x_262_);
lean_ctor_set(v___x_263_, 4, v___x_262_);
lean_ctor_set(v___x_263_, 5, v___x_262_);
v___x_264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3));
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_225_);
v___x_266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_262_);
lean_ctor_set(v___x_266_, 2, v___x_262_);
lean_ctor_set(v___x_266_, 3, v___x_262_);
lean_ctor_set(v___x_266_, 4, v___x_262_);
lean_ctor_set(v___x_266_, 5, v___x_262_);
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = lean_mk_empty_array_with_capacity(v___x_267_);
v___x_269_ = lean_array_push(v___x_268_, v___x_263_);
v___x_270_ = lean_array_push(v___x_269_, v___x_266_);
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4));
v___x_272_ = 4;
v___x_273_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_stx_203_, v___x_270_, v___x_262_, v___x_271_, v___x_262_, v___x_272_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_273_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v___x_273_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_dec(v___x_273_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_box(v___x_204_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
else
{
lean_dec(v_a_225_);
lean_dec(v_seq_220_);
lean_dec(v_stx_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
return v___x_230_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_del_object(v___x_222_);
lean_dec(v_seq_220_);
lean_dec(v_a_217_);
lean_dec(v_stx_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v_a_197_);
v_a_292_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_224_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_224_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
else
{
lean_object* v_gs_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_217_);
lean_dec(v_stx_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v_a_197_);
v_gs_301_ = lean_ctor_get(v_a_219_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_349_ == 0)
{
v___x_303_ = v_a_219_;
v_isShared_304_ = v_isSharedCheck_349_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_gs_301_);
lean_dec(v_a_219_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_349_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
if (lean_obj_tag(v_gs_301_) == 1)
{
lean_object* v_head_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_345_; 
v_head_305_ = lean_ctor_get(v_gs_301_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_gs_301_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_gs_301_, 1);
lean_dec(v_unused_346_);
v___x_307_ = v_gs_301_;
v_isShared_308_ = v_isSharedCheck_345_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_head_305_);
lean_dec(v_gs_301_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_345_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_head_305_);
v___x_310_ = v___x_303_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_head_305_);
v___x_310_ = v_reuseFailAlloc_344_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_mkResult(v_params_205_, v___x_310_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
v___x_313_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_312_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_313_);
v___x_315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 7);
lean_ctor_set(v___x_307_, 1, v_a_314_);
lean_ctor_set(v___x_307_, 0, v___x_315_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_a_314_);
v___x_317_ = v_reuseFailAlloc_327_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v___x_318_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v___x_317_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
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
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_307_);
v_a_328_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_313_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_313_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_del_object(v___x_307_);
v_a_336_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_311_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_311_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_del_object(v___x_303_);
lean_dec(v_gs_301_);
v___x_347_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8);
v___x_348_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v___x_347_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_217_);
lean_dec(v_stx_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v_a_197_);
v_a_350_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_218_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_218_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_stx_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v_a_198_);
lean_dec_ref(v_a_197_);
v_a_358_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_216_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_216_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(lean_object** _args){
lean_object* v_a_366_ = _args[0];
lean_object* v_a_367_ = _args[1];
lean_object* v___x_368_ = _args[2];
lean_object* v___x_369_ = _args[3];
lean_object* v___x_370_ = _args[4];
lean_object* v___x_371_ = _args[5];
lean_object* v_stx_372_ = _args[6];
lean_object* v___x_373_ = _args[7];
lean_object* v_params_374_ = _args[8];
lean_object* v___y_375_ = _args[9];
lean_object* v___y_376_ = _args[10];
lean_object* v___y_377_ = _args[11];
lean_object* v___y_378_ = _args[12];
lean_object* v___y_379_ = _args[13];
lean_object* v___y_380_ = _args[14];
lean_object* v___y_381_ = _args[15];
lean_object* v___y_382_ = _args[16];
lean_object* v___y_383_ = _args[17];
lean_object* v___y_384_ = _args[18];
_start:
{
uint8_t v___x_23232__boxed_385_; lean_object* v_res_386_; 
v___x_23232__boxed_385_ = lean_unbox(v___x_373_);
v_res_386_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(v_a_366_, v_a_367_, v___x_368_, v___x_369_, v___x_370_, v___x_371_, v_stx_372_, v___x_23232__boxed_385_, v_params_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v_params_374_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(lean_object* v___f_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_387_, v___y_388_, v___y_389_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v___x_402_; 
v___x_402_ = lean_unbox(v_a_398_);
lean_dec(v_a_398_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_box(0);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_del_object(v___x_400_);
v___x_407_ = lean_box(0);
v___x_408_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_407_, v___y_389_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
return v___x_408_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_a_410_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_397_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_397_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(lean_object* v___f_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(v___f_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v_stx_434_, uint8_t v___x_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_429_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_447_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v___x_447_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_437_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_params_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref(v___x_447_);
v_params_449_ = lean_ctor_get(v___y_436_, 4);
v___x_450_ = lean_box(v___x_435_);
lean_inc_ref(v_params_449_);
v___f_451_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed), 19, 9);
lean_closure_set(v___f_451_, 0, v_a_448_);
lean_closure_set(v___f_451_, 1, v_a_446_);
lean_closure_set(v___f_451_, 2, v___x_430_);
lean_closure_set(v___f_451_, 3, v___x_431_);
lean_closure_set(v___f_451_, 4, v___x_432_);
lean_closure_set(v___f_451_, 5, v___x_433_);
lean_closure_set(v___f_451_, 6, v_stx_434_);
lean_closure_set(v___f_451_, 7, v___x_450_);
lean_closure_set(v___f_451_, 8, v_params_449_);
v___f_452_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed), 10, 1);
lean_closure_set(v___f_452_, 0, v___f_451_);
v___x_453_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_452_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec_ref(v___y_436_);
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_a_446_);
lean_dec_ref(v___y_436_);
lean_dec(v_stx_434_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v___x_432_);
lean_dec_ref(v___x_431_);
lean_dec_ref(v___x_430_);
v_a_454_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_447_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_447_);
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
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v___y_436_);
lean_dec(v_stx_434_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v___x_432_);
lean_dec_ref(v___x_431_);
lean_dec_ref(v___x_430_);
v_a_462_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_474_ == 0)
{
v___x_464_ = v___x_445_;
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_445_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_ref_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v_ref_466_ = lean_ctor_get(v___y_442_, 5);
v___x_467_ = lean_io_error_to_string(v_a_462_);
v___x_468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = l_Lean_MessageData_ofFormat(v___x_468_);
lean_inc(v_ref_466_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_466_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_470_);
v___x_472_ = v___x_464_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v_stx_480_, lean_object* v___x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
uint8_t v___x_23671__boxed_491_; lean_object* v_res_492_; 
v___x_23671__boxed_491_ = lean_unbox(v___x_481_);
v_res_492_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(v___x_475_, v___x_476_, v___x_477_, v___x_478_, v___x_479_, v_stx_480_, v___x_23671__boxed_491_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(lean_object* v___y_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v_stx_498_, uint8_t v___x_499_, lean_object* v_only_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_params_510_; lean_object* v___x_511_; uint8_t v___y_513_; 
v_params_510_ = lean_ctor_get(v___y_501_, 4);
lean_inc_ref(v_params_510_);
v___x_511_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_493_);
if (lean_obj_tag(v_only_500_) == 0)
{
uint8_t v___x_518_; 
v___x_518_ = 0;
v___y_513_ = v___x_518_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___x_499_;
goto v___jp_512_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(10000u);
v___x_515_ = lean_box(v___x_499_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed), 16, 7);
lean_closure_set(v___f_516_, 0, v___x_514_);
lean_closure_set(v___f_516_, 1, v___x_494_);
lean_closure_set(v___f_516_, 2, v___x_495_);
lean_closure_set(v___f_516_, 3, v___x_496_);
lean_closure_set(v___f_516_, 4, v___x_497_);
lean_closure_set(v___f_516_, 5, v_stx_498_);
lean_closure_set(v___f_516_, 6, v___x_515_);
v___x_517_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_510_, v___x_511_, v___y_513_, v___f_516_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v___x_511_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(lean_object** _args){
lean_object* v___y_519_ = _args[0];
lean_object* v___x_520_ = _args[1];
lean_object* v___x_521_ = _args[2];
lean_object* v___x_522_ = _args[3];
lean_object* v___x_523_ = _args[4];
lean_object* v_stx_524_ = _args[5];
lean_object* v___x_525_ = _args[6];
lean_object* v_only_526_ = _args[7];
lean_object* v___y_527_ = _args[8];
lean_object* v___y_528_ = _args[9];
lean_object* v___y_529_ = _args[10];
lean_object* v___y_530_ = _args[11];
lean_object* v___y_531_ = _args[12];
lean_object* v___y_532_ = _args[13];
lean_object* v___y_533_ = _args[14];
lean_object* v___y_534_ = _args[15];
lean_object* v___y_535_ = _args[16];
_start:
{
uint8_t v___x_23772__boxed_536_; lean_object* v_res_537_; 
v___x_23772__boxed_536_ = lean_unbox(v___x_525_);
v_res_537_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(v___y_519_, v___x_520_, v___x_521_, v___x_522_, v___x_523_, v_stx_524_, v___x_23772__boxed_536_, v_only_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec(v_only_526_);
lean_dec_ref(v___y_519_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(size_t v_sz_538_, size_t v_i_539_, lean_object* v_bs_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_bs_540_);
return v___x_542_;
}
else
{
lean_object* v_v_543_; lean_object* v___x_544_; lean_object* v_bs_x27_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_v_543_ = lean_array_uget(v_bs_540_, v_i_539_);
v___x_544_ = lean_unsigned_to_nat(0u);
v_bs_x27_545_ = lean_array_uset(v_bs_540_, v_i_539_, v___x_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_539_, v___x_546_);
v___x_548_ = lean_array_uset(v_bs_x27_545_, v_i_539_, v_v_543_);
v_i_539_ = v___x_547_;
v_bs_540_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(lean_object* v_stx_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0));
v___x_580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1));
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3));
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5));
lean_inc(v_stx_569_);
v___x_584_ = l_Lean_Syntax_isOfKind(v_stx_569_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec(v_stx_569_);
v___x_585_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = l_Lean_Syntax_getArg(v_stx_569_, v___x_586_);
v___x_588_ = l_Lean_Syntax_getArgs(v___x_587_);
lean_dec(v___x_587_);
v_sz_589_ = lean_array_size(v___x_588_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_589_, v___x_590_, v___x_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; 
lean_dec(v_stx_569_);
v___x_592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_592_;
}
else
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_640_; 
v_val_593_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_640_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_640_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_640_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v_only_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(2u);
v___x_630_ = l_Lean_Syntax_getArg(v_stx_569_, v___x_629_);
v___x_631_ = l_Lean_Syntax_isNone(v___x_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
lean_inc(v___x_630_);
v___x_632_ = l_Lean_Syntax_matchesNull(v___x_630_, v___x_586_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v___x_630_);
lean_del_object(v___x_595_);
lean_dec(v_val_593_);
lean_dec(v_stx_569_);
v___x_633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v_only_635_; lean_object* v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v_only_635_ = l_Lean_Syntax_getArg(v___x_630_, v___x_634_);
lean_dec(v___x_630_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_only_635_);
v___x_637_ = v___x_595_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_only_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_only_612_ = v___x_637_;
v___y_613_ = v_a_570_;
v___y_614_ = v_a_571_;
v___y_615_ = v_a_572_;
v___y_616_ = v_a_573_;
v___y_617_ = v_a_574_;
v___y_618_ = v_a_575_;
v___y_619_ = v_a_576_;
v___y_620_ = v_a_577_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v___x_630_);
lean_del_object(v___x_595_);
v___x_639_ = lean_box(0);
v_only_612_ = v___x_639_;
v___y_613_ = v_a_570_;
v___y_614_ = v_a_571_;
v___y_615_ = v_a_572_;
v___y_616_ = v_a_573_;
v___y_617_ = v_a_574_;
v___y_618_ = v_a_575_;
v___y_619_ = v_a_576_;
v___y_620_ = v_a_577_;
goto v___jp_611_;
}
v___jp_597_:
{
lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v___x_608_ = lean_box(v___x_584_);
v___f_609_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed), 17, 8);
lean_closure_set(v___f_609_, 0, v___y_607_);
lean_closure_set(v___f_609_, 1, v___x_579_);
lean_closure_set(v___f_609_, 2, v___x_580_);
lean_closure_set(v___f_609_, 3, v___x_581_);
lean_closure_set(v___f_609_, 4, v___x_582_);
lean_closure_set(v___f_609_, 5, v_stx_569_);
lean_closure_set(v___f_609_, 6, v___x_608_);
lean_closure_set(v___f_609_, 7, v___y_598_);
v___x_610_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(v_val_593_, v___f_609_, v___y_604_, v___y_601_, v___y_605_, v___y_603_, v___y_600_, v___y_602_, v___y_606_, v___y_599_);
lean_dec(v_val_593_);
return v___x_610_;
}
v___jp_611_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_unsigned_to_nat(3u);
v___x_622_ = l_Lean_Syntax_getArg(v_stx_569_, v___x_621_);
v___x_623_ = l_Lean_Syntax_isNone(v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
lean_inc(v___x_622_);
v___x_624_ = l_Lean_Syntax_matchesNull(v___x_622_, v___x_621_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
lean_dec(v___x_622_);
lean_dec(v_only_612_);
lean_dec(v_val_593_);
lean_dec(v_stx_569_);
v___x_625_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v_params_x3f_627_; 
v___x_626_ = l_Lean_Syntax_getArg(v___x_622_, v___x_586_);
lean_dec(v___x_622_);
v_params_x3f_627_ = l_Lean_Syntax_getArgs(v___x_626_);
lean_dec(v___x_626_);
v___y_598_ = v_only_612_;
v___y_599_ = v___y_620_;
v___y_600_ = v___y_617_;
v___y_601_ = v___y_614_;
v___y_602_ = v___y_618_;
v___y_603_ = v___y_616_;
v___y_604_ = v___y_613_;
v___y_605_ = v___y_615_;
v___y_606_ = v___y_619_;
v___y_607_ = v_params_x3f_627_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec(v___x_622_);
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6));
v___y_598_ = v_only_612_;
v___y_599_ = v___y_620_;
v___y_600_ = v___y_617_;
v___y_601_ = v___y_614_;
v___y_602_ = v___y_618_;
v___y_603_ = v___y_616_;
v___y_604_ = v___y_613_;
v___y_605_ = v___y_615_;
v___y_606_ = v___y_619_;
v___y_607_ = v___x_628_;
goto v___jp_597_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(lean_object* v_stx_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(v_stx_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(lean_object* v_00_u03b1_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v_msg_653_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(lean_object* v_00_u03b1_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_00_u03b1_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1(){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5));
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15));
v___x_722_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed), 10, 0);
v___x_723_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_719_, v___x_720_, v___x_721_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
return v_res_725_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
